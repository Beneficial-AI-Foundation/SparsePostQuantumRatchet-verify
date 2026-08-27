/**
 * Download and install the charon + aeneas binaries from a GitHub release.
 *
 * Steps:
 * 1. Check dependencies (curl, tar, rustup)
 * 2. Download the release bundle for this platform
 * 3. Extract it into .aeneas/
 * 4. Install the Rust nightly that the bundled charon-driver requires
 *
 * Skips the download if the installed aeneas already reports the pinned release tag.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import ora from "ora";
import { loadConfig } from "./lib/config.js";
import { run } from "./lib/shell.js";
import { findBinary } from "./lib/paths.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

// ── Paths ─────────────────────────────────────────────────────────────

function getAeneasDir(root: string): string {
  return path.join(root, ".aeneas");
}

// ── Release assets ────────────────────────────────────────────────────

/**
 * The release asset for the current platform.
 */
function getAssetName(): string {
  const key = `${process.platform}-${process.arch}`;
  const assets: Record<string, string> = {
    "linux-x64": "aeneas-linux-x86_64.tar.gz",
    "linux-arm64": "aeneas-linux-aarch64.tar.gz",
    "darwin-arm64": "aeneas-macos-aarch64.tar.gz",
  };

  const asset = assets[key];
  if (!asset) {
    throw new Error(
      `No aeneas release build for ${key}. Supported: ${Object.keys(assets).join(", ")}. ` +
        `Build aeneas from source and place the 'aeneas', 'charon' and 'charon-driver' ` +
        `binaries plus 'backends/' in .aeneas/`,
    );
  }
  return asset;
}

function getAssetUrl(repo: string, tag: string, asset: string): string {
  // https://github.com/AeneasVerif/aeneas.git -> https://github.com/AeneasVerif/aeneas
  const base = repo.replace(/\.git$/, "");
  return `${base}/releases/download/${tag}/${asset}`;
}

// ── Version check ─────────────────────────────────────────────────────

/**
 * The release tag reported by the installed aeneas, or null if it is absent or unreadable.
 * A release build prints `aeneas <tag>`.
 */
async function getInstalledTag(root: string): Promise<string | null> {
  const aeneasBin = findBinary("aeneas", root);
  if (!aeneasBin) return null;

  try {
    const output = await run(aeneasBin, ["-version"], { silent: true });
    return output.trim().replace(/^aeneas\s+/, "") || null;
  } catch {
    return null;
  }
}

// ── Dependencies ──────────────────────────────────────────────────────

async function checkDependencies(): Promise<void> {
  const spinner = ora("Checking dependencies...").start();
  const deps = ["curl", "tar", "rustup"];
  const missing: string[] = [];

  for (const dep of deps) {
    try {
      await run("which", [dep], { silent: true });
    } catch {
      missing.push(dep);
    }
  }

  if (missing.length > 0) {
    spinner.fail();
    throw new Error(`Missing dependencies: ${missing.join(", ")}`);
  }
  spinner.succeed("Dependencies OK");
}

// ── Rust toolchain ────────────────────────────────────────────────────

function parseToolchainChannel(filePath: string): string | null {
  if (!fs.existsSync(filePath)) return null;
  const content = fs.readFileSync(filePath, "utf-8");
  const match = content.match(/channel\s*=\s*"?([^"\s]+)"?/);
  return match ? match[1] : null;
}

/**
 * The bundled charon-driver is a rustc driver built against a specific nightly, so that exact
 * toolchain must be installed locally with `rustc-dev`. The bundle ships the `rust-toolchain`
 * file naming it.
 */
async function setupRustToolchain(aeneasDir: string): Promise<void> {
  const toolchain = parseToolchainChannel(path.join(aeneasDir, "rust-toolchain")) ?? "nightly";

  const spinner = ora(`Installing Rust ${toolchain}...`).start();
  await run("rustup", ["toolchain", "install", toolchain], { silent: true });
  await run("rustup", ["component", "add", "--toolchain", toolchain, "rustfmt", "rustc-dev"], {
    silent: true,
  });
  spinner.succeed(`Rust ${toolchain} ready`);
}

// ── Download and extract ──────────────────────────────────────────────

async function downloadAndExtract(url: string, aeneasDir: string): Promise<void> {
  // Wipe first: the previous build-from-source layout had .aeneas/aeneas as a directory,
  // whereas the bundle extracts it as a file.
  fs.rmSync(aeneasDir, { recursive: true, force: true });
  fs.mkdirSync(aeneasDir, { recursive: true });

  const archive = path.join(aeneasDir, "bundle.tar.gz");

  console.log(chalk.dim(`  ${url}`));
  // -sS rather than a progress bar: the carriage returns flood CI logs.
  const spinner = ora("Downloading...").start();
  await run("curl", ["-fL", "-sS", "-o", archive, url], { silent: true });

  spinner.text = "Extracting...";
  await run("tar", ["-xzf", archive, "-C", aeneasDir], { silent: true });
  fs.rmSync(archive, { force: true });
  spinner.succeed("Downloaded and extracted");
}

// ── Main ──────────────────────────────────────────────────────────────

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Install\n"));

  const { config, root } = loadConfig();
  const tag = config.aeneas.tag;
  const aeneasDir = getAeneasDir(root);

  // Check if already installed at the correct release
  const installed = await getInstalledTag(root);
  if (installed === tag && findBinary("charon", root)) {
    console.log(chalk.green(`Already up to date (${tag}). Skipping.`));
    return;
  }

  await checkDependencies();

  const asset = getAssetName();
  const url = getAssetUrl(config.aeneas.repo, tag, asset);

  console.log(chalk.bold(`\nDownloading ${tag} (${asset})...`));
  await downloadAndExtract(url, aeneasDir);

  await setupRustToolchain(aeneasDir);

  // Verify binaries exist and report the expected release
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);

  if (!charonBin || !aeneasBin) {
    throw new Error("Download completed but binaries not found at expected paths");
  }

  const actual = await getInstalledTag(root);
  if (actual !== tag) {
    throw new Error(`Version mismatch: expected '${tag}', got '${actual}'`);
  }

  console.log(chalk.green("\nInstall complete!"));
  console.log(`  Charon: ${charonBin}`);
  console.log(`  Aeneas: ${aeneasBin}`);

  syncLeanToolchain(root);
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
