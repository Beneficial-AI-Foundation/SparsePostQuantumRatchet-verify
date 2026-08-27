import path from "node:path";
import fs from "node:fs";

/**
 * Resolve a binary from the extracted aeneas release bundle.
 *
 * Bundle layout:
 *   .aeneas/aeneas
 *   .aeneas/charon
 *   .aeneas/charon-driver
 *   .aeneas/rust-toolchain
 *   .aeneas/backends/...
 */
export function findBinary(name: "charon" | "aeneas", root: string): string | null {
  const p = path.join(root, ".aeneas", name);
  return fs.existsSync(p) ? p : null;
}
