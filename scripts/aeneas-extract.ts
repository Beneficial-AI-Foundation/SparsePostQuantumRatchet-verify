/**
 * Run the full extraction pipeline: patches -> Charon -> revert patches -> Aeneas -> Tweaks.
 *
 * All charon options come from aeneas-config.yml and are passed as CLI args. The Rust translation
 * patches in `patches_dir` are applied one by one before Charon and reverted (in reverse order)
 * right after it, also on failure or interrupt, so the Rust sources stay upstream.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { loadConfig } from "./lib/config.js";
import { findBinary } from "./lib/paths.js";
import { run, runStreaming } from "./lib/shell.js";
import { applyPatches, listPatches, revertPatches } from "./lib/patches.js";
import { applyTweaks, warnUnmatchedTweaks } from "./lib/tweaks.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Extract\n"));

  const { config, root } = loadConfig();

  // Resolve binaries
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);

  if (!charonBin) {
    throw new Error("Charon binary not found. Run 'npm run aeneas-install' first.");
  }
  if (!aeneasBin) {
    throw new Error("Aeneas binary not found. Run 'npm run aeneas-install' first.");
  }
  const installed = (await run(aeneasBin, ["-version"])).trim();
  if (installed !== `aeneas ${config.aeneas.tag}`) {
    throw new Error(
      `Installed '${installed}' does not match the pinned tag '${config.aeneas.tag}' (lakefile.toml). ` +
        "Run 'npm run aeneas-install' first.",
    );
  }

  const llbcFile = `${config.crate.name}.llbc`;
  const llbcPath = path.join(root, llbcFile);
  const destDir = path.join(root, config.aeneas_args.dest);
  const outputDir = config.aeneas_args.subdir
    ? path.join(destDir, config.aeneas_args.subdir)
    : destDir;
  const logsDir = path.join(root, ".logs");

  // ── Step 1: Charon ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 1: Generating LLBC with Charon..."));

  const charonArgs: string[] = ["cargo"];

  if (config.charon.preset) {
    charonArgs.push(`--preset=${config.charon.preset}`);
  }
  if (config.charon.sysroot) {
    charonArgs.push(`--sysroot=${config.charon.sysroot}`);
  }
  if (config.charon.hide_marker_traits) {
    charonArgs.push("--hide-marker-traits");
  }
  for (const item of config.charon.start_from) {
    charonArgs.push("--start-from", item);
  }
  if (config.charon.start_from_pub) {
    charonArgs.push("--start-from-pub");
  }
  for (const item of config.charon.exclude) {
    charonArgs.push("--exclude", item);
  }
  for (const item of config.charon.opaque) {
    charonArgs.push("--opaque", item);
  }

  // Cargo args go after --
  if (config.charon.cargo_args.length > 0) {
    charonArgs.push("--", ...config.charon.cargo_args);
  }

  // Remove stale LLBC
  if (fs.existsSync(llbcPath)) {
    fs.unlinkSync(llbcPath);
  }

  fs.mkdirSync(logsDir, { recursive: true });

  // The Rust sources must be unmodified (the patches are written against them). Tools such as
  // rust-analyzer may rewrite Cargo.lock behind our back.
  const rustSources = ["src", "build.rs", "Cargo.toml", "Cargo.lock"];
  const dirty = (await run("git", ["diff", "--name-only", "--", ...rustSources], { cwd: root })).trim();
  if (dirty) {
    throw new Error(
      `The Rust sources are modified in the working tree:\n${dirty}\n` +
        `Restore them with: git checkout -- ${rustSources.join(" ")}`,
    );
  }

  // Apply the translation patches only for the duration of the Charon run.
  const patches = listPatches(path.join(root, config.patches_dir));
  console.log(chalk.bold(`  Applying ${patches.length} translation patch(es)...`));
  const applied = await applyPatches(root, patches);
  const onInterrupt = (): void => {
    revertPatches(root, applied)
      .catch((err) => console.error(chalk.red(err.message)))
      .finally(() => process.exit(130));
  };
  process.once("SIGINT", onInterrupt);
  process.once("SIGTERM", onInterrupt);
  try {
    await runStreaming(charonBin, charonArgs, {
      cwd: root,
      logFile: path.join(logsDir, "charon.log"),
    });
  } finally {
    process.removeListener("SIGINT", onInterrupt);
    process.removeListener("SIGTERM", onInterrupt);
    await revertPatches(root, applied);
    console.log(chalk.bold(`  Reverted ${patches.length} translation patch(es).`));
  }

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Failed to generate ${llbcFile}`);
  }

  console.log(chalk.green(`  LLBC generated: ${llbcFile}\n`));

  // ── Step 2: Aeneas ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 3: Generating Lean files with Aeneas..."));

  const aeneasArgs: string[] = [
    "-backend", "lean",
    ...config.aeneas_args.options.map((o) => `-${o}`),
    "-dest", destDir,
  ];
  if (config.aeneas_args.use_lean_modules === false) {
    aeneasArgs.push("-use-lean-modules", "false");
  }
  if (config.aeneas_args.subdir) {
    aeneasArgs.push("-subdir", config.aeneas_args.subdir);
  }
  aeneasArgs.push(llbcFile);

  fs.mkdirSync(outputDir, { recursive: true });

  await runStreaming(aeneasBin, aeneasArgs, {
    cwd: root,
    logFile: path.join(logsDir, "aeneas.log"),
  });

  console.log(chalk.green(`  Lean files generated in ${config.aeneas_args.dest}/\n`));

  // ── Step 3: Lean file tweaks ──────────────────────────────────────────────────
  if (config.tweaks.substitutions.length > 0 && config.tweaks.files.length > 0) {
    console.log(chalk.bold("Step 4: Applying tweaks to Lean files..."));

    const matchedPerFile: Set<number>[] = [];
    for (const file of config.tweaks.files) {
      const filePath = path.join(outputDir, file);
      if (!fs.existsSync(filePath)) {
        console.log(chalk.yellow(`  Warning: File not found, skipping: ${file}`));
        continue;
      }
      const matched = applyTweaks(filePath, config.tweaks.substitutions);
      matchedPerFile.push(matched);
      console.log(chalk.green(`  Tweaks applied to ${file} (${matched.size} substitutions matched)`));
    }
    warnUnmatchedTweaks(config.tweaks.substitutions, matchedPerFile);
    console.log();
  }

  // ── Step 4: Lean toolchain sync ─────────────────────────────────────
  syncLeanToolchain(root);

  console.log(chalk.green("Done."));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
