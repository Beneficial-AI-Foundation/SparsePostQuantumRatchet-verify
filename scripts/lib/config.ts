import fs from "node:fs";
import path from "node:path";
import yaml from "js-yaml";

export interface Substitution {
  find?: string;
  regex?: string;
  replace: string;
}

export interface AeneasConfig {
  aeneas: {
    /** Release tag, read from `lakefile.toml` (the single source of truth), not from the YAML. */
    tag: string;
    repo: string;
  };
  upstream: {
    repo: string;
    commit: string;
  };
  charon: {
    preset: string;
    sysroot: string;
    hide_marker_traits: boolean;
    cargo_args: string[];
    start_from: string[];
    start_from_pub?: boolean;
    exclude: string[];
    opaque: string[];
  };
  aeneas_args: {
    options: string[];
    dest: string;
    subdir?: string;
    use_lean_modules?: boolean;
  };
  crate: {
    dir: string;
    name: string;
  };
  /** Folder of Rust translation patches (one function per patch), applied only while extracting. */
  patches_dir: string;
  llbc_tweaks: {
    substitutions: Substitution[];
  };
  tweaks: {
    files: string[];
    substitutions: Substitution[];
  };
}

/**
 * Walk up from `from` to find the directory containing `aeneas-config.yml`.
 */
export function findProjectRoot(from?: string): string {
  let dir = from ?? process.cwd();
  while (true) {
    if (fs.existsSync(path.join(dir, "aeneas-config.yml"))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error("Could not find aeneas-config.yml in any parent directory");
    }
    dir = parent;
  }
}

/**
 * Load and validate aeneas-config.yml.
 */
export function loadConfig(root?: string): { config: AeneasConfig; root: string } {
  const projectRoot = root ?? findProjectRoot();
  const filePath = path.join(projectRoot, "aeneas-config.yml");

  if (!fs.existsSync(filePath)) {
    throw new Error(`Config file not found: ${filePath}`);
  }

  const raw = yaml.load(fs.readFileSync(filePath, "utf-8")) as Record<string, unknown>;
  if (!raw || typeof raw !== "object") {
    throw new Error("aeneas-config.yml is empty or invalid");
  }

  const config = raw as unknown as AeneasConfig;

  // Validate required fields
  if (!config.aeneas?.repo) throw new Error("Missing required field: aeneas.repo");
  if ((config.aeneas as { tag?: string }).tag) {
    throw new Error("aeneas.tag is no longer read from aeneas-config.yml: the tag is pinned only in lakefile.toml");
  }
  config.aeneas.tag = readLakefileAeneasTag(projectRoot);
  if (!config.crate?.dir) throw new Error("Missing required field: crate.dir");

  // Apply defaults
  config.upstream = config.upstream ?? { repo: "", commit: "" };
  config.charon = config.charon ?? {} as AeneasConfig["charon"];
  config.charon.preset = config.charon.preset ?? "aeneas";
  config.charon.sysroot = config.charon.sysroot ?? "default";
  config.charon.hide_marker_traits = config.charon.hide_marker_traits ?? false;
  config.charon.cargo_args = config.charon.cargo_args ?? [];
  config.charon.start_from = config.charon.start_from ?? [];
  config.charon.start_from_pub = config.charon.start_from_pub ?? false;
  config.charon.exclude = config.charon.exclude ?? [];
  config.charon.opaque = config.charon.opaque ?? [];
  config.aeneas_args = config.aeneas_args ?? {} as AeneasConfig["aeneas_args"];
  config.aeneas_args.options = config.aeneas_args.options ?? [];
  config.aeneas_args.dest = config.aeneas_args.dest ?? "output";
  config.crate.name = config.crate.name ?? config.crate.dir.replace(/-/g, "_");
  config.llbc_tweaks = config.llbc_tweaks ?? { substitutions: [] };
  config.llbc_tweaks.substitutions = config.llbc_tweaks.substitutions ?? [];
  config.tweaks = config.tweaks ?? { files: [], substitutions: [] };
  config.tweaks.files = config.tweaks.files ?? [];
  config.tweaks.substitutions = config.tweaks.substitutions ?? [];
  config.patches_dir = config.patches_dir ?? "translation-patches";

  return { config, root: projectRoot };
}

/**
 * The Aeneas release tag: the `rev` of the `[[require]]` entry named `aeneas` in `lakefile.toml`.
 * This is the single source of truth for both the Lean library and the downloaded binaries.
 */
export function readLakefileAeneasTag(root: string): string {
  const lakefile = path.join(root, "lakefile.toml");
  let name = "";
  for (const line of fs.readFileSync(lakefile, "utf-8").split("\n")) {
    if (/^\s*\[/.test(line)) name = "";
    const n = line.match(/^\s*name\s*=\s*"([^"]*)"/);
    if (n) name = n[1];
    const r = line.match(/^\s*rev\s*=\s*"([^"]*)"/);
    if (r && name === "aeneas") return r[1];
  }
  throw new Error("Could not find the aeneas `rev` in lakefile.toml");
}
