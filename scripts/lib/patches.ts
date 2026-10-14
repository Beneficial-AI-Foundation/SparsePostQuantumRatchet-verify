/**
 * Rust translation patches: one function per patch, applied only while extracting.
 *
 * Patches are applied one by one and recorded, so that exactly the applied ones can be reverted,
 * in reverse order, also when a later step fails (a single multi-patch `git apply -R` is not
 * atomic and can leave the sources half-patched).
 */

import fs from "node:fs";
import path from "node:path";
import { execa } from "execa";

/** The patch files in `dir`, sorted by name. An absent or empty folder gives no patches. */
export function listPatches(dir: string): string[] {
  if (!fs.existsSync(dir)) return [];
  return fs
    .readdirSync(dir)
    .filter((f) => f.endsWith(".patch"))
    .sort()
    .map((f) => path.join(dir, f));
}

async function git(root: string, args: string[]): Promise<void> {
  const r = await execa("git", args, { cwd: root, reject: false });
  if (r.exitCode !== 0) {
    throw new Error(`git ${args.join(" ")} failed:\n${r.stderr || r.stdout}`);
  }
}

/** Check that `patch` applies (or, with `reverse`, reverts) cleanly on the current tree. */
export async function checkPatch(root: string, patch: string, reverse = false): Promise<boolean> {
  const args = ["apply", "--check", ...(reverse ? ["-R"] : []), patch];
  const r = await execa("git", args, { cwd: root, reject: false });
  return r.exitCode === 0;
}

/**
 * Apply `patches` one by one. Returns the list of applied patches (in application order). If one
 * fails, the ones already applied are reverted before the error is rethrown.
 */
export async function applyPatches(root: string, patches: string[]): Promise<string[]> {
  const applied: string[] = [];
  try {
    for (const p of patches) {
      await git(root, ["apply", p]);
      applied.push(p);
    }
  } catch (err) {
    await revertPatches(root, applied);
    throw err;
  }
  return applied;
}

/**
 * Revert `applied` in reverse order. Attempts every patch even if one fails, then reports all
 * failures together (a failure here leaves the sources modified and needs attention).
 */
export async function revertPatches(root: string, applied: string[]): Promise<void> {
  const failures: string[] = [];
  for (const p of [...applied].reverse()) {
    try {
      await git(root, ["apply", "-R", p]);
    } catch (err) {
      failures.push((err as Error).message);
    }
  }
  applied.length = 0;
  if (failures.length > 0) {
    throw new Error(`Reverting patches failed; the Rust sources are still modified:\n${failures.join("\n")}`);
  }
}
