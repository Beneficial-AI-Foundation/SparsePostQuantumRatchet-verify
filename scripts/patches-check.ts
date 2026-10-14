/**
 * Check the Rust translation patches:
 *   1. each patch applies on its own to the clean tree;
 *   2. all patches apply and revert, in forward and in reverse order;
 *   3. the working tree is unchanged afterwards.
 */

import path from "node:path";
import chalk from "chalk";
import { execa } from "execa";
import { loadConfig } from "./lib/config.js";
import { applyPatches, checkPatch, listPatches, revertPatches } from "./lib/patches.js";

async function status(root: string): Promise<string> {
  return (await execa("git", ["status", "--porcelain"], { cwd: root })).stdout;
}

async function main(): Promise<void> {
  const { config, root } = loadConfig();
  const patches = listPatches(path.join(root, config.patches_dir));
  console.log(chalk.bold(`\nChecking ${patches.length} translation patch(es)\n`));
  const before = await status(root);
  let ok = true;

  for (const p of patches) {
    if (!(await checkPatch(root, p))) {
      console.log(chalk.red(`  does not apply on its own: ${path.basename(p)}`));
      ok = false;
    }
  }

  for (const [label, order] of [
    ["forward", patches],
    ["reverse", [...patches].reverse()],
  ] as const) {
    try {
      const applied = await applyPatches(root, [...order]);
      await revertPatches(root, applied);
      console.log(chalk.green(`  all apply and revert (${label} order)`));
    } catch (err) {
      console.log(chalk.red(`  ${label} order: ${(err as Error).message}`));
      ok = false;
    }
  }

  if ((await status(root)) !== before) {
    console.log(chalk.red("  the working tree changed during the check"));
    ok = false;
  }

  if (!ok) {
    console.error(chalk.red("\nPatch check failed."));
    process.exit(1);
  }
  console.log(chalk.green("\nPatch check passed."));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
