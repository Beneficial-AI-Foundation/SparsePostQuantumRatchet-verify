# Extracting a Rust crate to Lean with Charon/Aeneas: the procedure

How the fullest possible translation of curve25519-dalek was obtained (2026-10-09/10), written
as a procedure to repeat on another crate. Concrete examples are from this repository:
`scripts/aeneas-{install,translate}.sh`, `curve25519-dalek/Cargo.toml`
(`[package.metadata.charon]`), `curve25519-dalek/translation-patches/`,
`.github/workflows/lean-translation.yml`, the "Translation" section of `verif-guidelines.md`.

## 1. Principles

1. **The upstream source stays untouched.** Every Rust change needed for the translation lives
   in a patch file, applied only while translating and reverted afterwards.
2. **Zero post-translation tweaks.** The generated `Types.lean`, `Funs.lean` and
   `translation.json` are committed exactly as Aeneas emits them. CI re-translates and fails if
   they differ.
3. **Translate everything that can matter for verification.** The decision rule for each item
   that does not translate as is:
   - **exclude**: only items that will never be verified *and* that nothing verified calls
     (here: `Debug`, `Hash`, derived `Eq` impls);
   - **opaque**: only for items verification needs but which we deliberately do not translate,
     even though it would be possible (here: none in the end);
   - **patch**: everything else.

   The user's wording: "we will exclude everything we will never care about for verification.
   then opaque is only to be used in very limited case if for some reason it is important for
   verification but we don't want to translate it, even if it is possible. in all other cases we
   will use patches to make the translation work".
4. **Patches preserve behaviour.** Any difference must be stated in the patch header, and the
   user decides case by case whether it is acceptable.
5. **Each patch is auditable on its own:** one function per patch, a short header, and the whole
   function in the diff.
6. **Hand-written Lean is minimal and trusted explicitly.** External functions are `opaque`
   signatures plus spec axioms, never `axiom` signatures, so that `#print axioms` lists exactly
   what is trusted.
7. **Re-test after every Aeneas release.** New releases fix limitations, so patches may become
   unnecessary. They also occasionally break something that worked.

## 2. Setup

### 2.1 Pin Aeneas to a release

- Put the Aeneas Lean library in `lakefile.toml` with `rev` set to a GitHub **release tag**
  (`nightly-YYYY.MM.DD-<hash>`). It is the single source of truth: the scripts read it, and the
  binaries are downloaded from that release. Add a comment saying so, and run
  `lake update aeneas` after changing it.
- `scripts/aeneas-install.sh` (copy from this repository, unchanged):
  - reads the tag with
    `awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' lakefile.toml`;
  - downloads `aeneas-<os>-<arch>.tar.gz` from the release into `.aeneas/` unless
    `.aeneas/aeneas -version` already prints `aeneas <tag>` (idempotent, 0.3 s when current);
  - installs the Rust nightly with `rustc-dev` that `charon-driver` needs, from the bundle's
    `rust-toolchain`, using `rustup toolchain install --no-self-update`;
  - copies `.aeneas/backends/lean/lean-toolchain` to the project's `lean-toolchain`.
- `.gitignore`: `.aeneas/`, `.llbc/`, `FunsExternal_Template.lean`, `TypesExternal_Template.lean`.
- `.gitattributes`: `*.rs diff=rust`. **Required**: without it `git diff -W` treats whole `impl`
  blocks as "the function", and patches of neighbouring methods overlap.

### 2.2 The translation script

`scripts/aeneas-translate.sh` (copy and adapt the crate name, features and `--cfg`s):

1. `set -euo pipefail`; refuse to run unless `.aeneas/aeneas -version` matches the pinned tag.
2. Apply the patches **one by one**, recording each in an array. A `trap revert EXIT` reverts
   exactly the applied ones **in reverse order**, also on failure. Use `shopt -s nullglob` so an
   empty patch folder works. (A single multi-patch `git apply -R` is not atomic and left `src/`
   half-patched once.)
3. `unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS`, because the latter overrides per-target flags.
4. Run Charon in the crate directory:
   `charon cargo --preset=aeneas [--targets …] --dest-file ../.llbc/<crate>.llbc -- --locked --no-default-features --features <list>`.
   - `--locked` ties the run to `Cargo.lock`.
   - Explicit targets make the host irrelevant.
5. Run Aeneas:
   `aeneas -backend lean -split-files -emit-json -namespace <LeanNamespace> -dest <crate>/lean -subdir <LibName> .llbc/<crate>.llbc`.
   - `-split-files` gives `Types`, `Funs` and the `*External_Template` files.
   - `-emit-json` gives `translation.json`.
   - `-namespace` puts the translation in a Lean-style namespace (`Curve25519Dalek`). The Rust
     path then appears only in doc comments and `rust_fun` strings.
6. Exit status: strict. Do not accept a nonzero Aeneas exit even if the files were written.
7. Check determinism once: run twice and compare bytes; grep the output for `/tmp/`, `/home/`
   and `.json`. Stdlib paths show up as `/rustc/…` and registry paths as `/cargo/registry/…`,
   which is fine.

Charon's settings go in the crate's `Cargo.toml`, under `[package.metadata.charon]`, with keys
`start_from`, `exclude` and `opaque`. Add a comment above `exclude` and above `opaque` stating
the rule from principle 3.

### 2.3 CI: the committed translation is current

`.github/workflows/lean-translation.yml` (copy and adapt the paths):
- Trigger on the Rust sources, both `Cargo.toml`s, `Cargo.lock`, `build.rs`, the patches, the
  generated Lean directory, `translation.json`, the scripts, `lakefile.toml`, `lean-toolchain`
  and the workflow itself.
- Cache `.aeneas`, `~/.rustup/toolchains/nightly-*` and `~/.rustup/update-hashes/nightly-*`,
  keyed on OS, arch and tag.
  - Use separate `actions/cache/restore` and `actions/cache/save` steps, so the cache is saved
    even when the freshness check fails.
- Run install, then translate, then fail if `git status --porcelain` is non-empty, printing
  `git diff | head -200`.
- Also set `permissions: contents: read`, `concurrency` with cancel-in-progress, and
  `timeout-minutes`.

A separate Lean build workflow runs `lake build --wfail` on the libraries, and
`lake exe runLinter` on the **hand-written** libraries. The generated code can't be linted.

## 3. Procedure

### Step 1: First translation, with nothing excluded

Run the translation with empty `exclude`/`opaque` and no patches, and record every failure.
- **Aeneas errors:**
  `tr '\r' '\n' < log | sed 's/\x1b\[[0-9;]*m//g' | grep -aE '^\[Error' | sort | uniq -c`.
  - Errors saying "Could not lookup the translated function, probably because of an error which
    happened before" are knock-on errors: fix the root ones first.
- **Lean errors:** build `Funs.lean` with no error limit (Lean stops at 100 by default). Map each
  error to the enclosing generated definition, and through its doc comment to the Rust item.
  Group the errors by Rust item.
- **Scope check:** grep the generated `Funs.lean` for unmodelled library calls (iterator
  adapters etc.) to see where they are used.
- If an older project or earlier attempt exists, survey what it verified and how it configured
  Charon. That informs which items matter.

### Step 2: Decide the scope with the user

For each failing item, propose exclude / opaque / patch using the rule in principle 3, and ask
the user with a short list of options. Typical decisions:
- **Features:** translate the default features; decide feature by feature (here `alloc`,
  `zeroize`, `precomputed-tables`).
- **Trait impls to exclude:** formatting (`Debug`, uses `core::fmt::Formatter`), `Hash` (uses
  `core::hash::Hasher`), marker traits (derived `Eq`).
  - Before excluding a trait impl, check that nothing translated calls it. Excluding the
    `Zeroize` impls here broke three functions (`Could not find: trait_impl_id`), so they were
    kept.
- **Local types:** a derived impl on a type local to a function needs a pattern like
  `crate::module::_::function::{impl core::fmt::Debug for _}`.

### Step 3: Write the patches

For each item to patch, find the smallest rewrite that Aeneas and the Lean library handle, keep
behaviour identical, and generate the patch file (section 4).
- **Experiment first on a minimal function.** For example, which loop shapes translate, or
  whether a closure works where a function pointer does not.
- **Prefer a patch to a new hand-written external.**
- **Don't accept "impossible" too early.** Twice here a first "no behaviour-identical rewrite
  exists" / "Charon cannot do this" was wrong after more thought: the `Copy` inner array allowed
  a static copy, and custom JSON target specs gave per-feature targets.

### Step 4: Iterate to green

After each batch:
1. run translate (exit 0);
2. run `lake build` of the translation (warnings as errors);
3. run `cargo test` with all patches applied, in debug and release;
4. run `cargo check` with no new warnings;
5. run the dependent crates' tests if any;
6. check that `git status` shows `src/` clean.

New failures that only appear once more is translated are normal. Here, a `scalar` variable
name clashed with the `scalar` module (aeneas#1098) in newly translated functions; the fix was a
rename inside those patches.

### Step 5: Necessity check (each patch must be needed)

For each patch: move it out of the folder, translate, build, and classify it as
"needed (aeneas)", "needed (lean)" or "NOT NEEDED"; then restore it. Run this in the background;
it took about 20 minutes for 27 patches.

On the first pass after a release bump:
- 6 of 17 patches were dropped because the Aeneas bugs had been fixed;
- 5 more were dropped because their functions were opaque, so they had no effect.

Re-run the check after every Aeneas update. Sketch:

```bash
for p in <crate>/translation-patches/*.patch; do
  mv "$p" /tmp/held.patch
  if ! ./scripts/aeneas-translate.sh > /tmp/t.log 2>&1; then r="needed (aeneas)"
  elif ! lake build <LibName> > /tmp/b.log 2>&1; then r="needed (lean)"
  else r="NOT NEEDED"; fi
  mv /tmp/held.patch "$p"; echo "$(basename $p): $r"
done
./scripts/aeneas-translate.sh   # restore the committed output
```

### Step 6: Independent audit of the patches (section 5)

### Step 7: External files (section 6)

### Step 8: Multi-configuration translation, if needed (section 7)

### Step 9: Commit the generated files and turn on CI

Commit `Types.lean`, `Funs.lean`, `translation.json`, the External files, the patches,
`.gitattributes`, the scripts and the workflows.

## 4. Patch files

### Location and naming

- Location: `<crate>/translation-patches/`. Note that `cargo package` would include them.
- File name: `<file-stem>-<function>.patch`.
  - Add `-<Type>` before the function only when the name alone is ambiguous within that Rust
    file: `edwards-EdwardsPoint-sum` but `ristretto-sum`.
  - Free functions take no type (`variable_base-mul`).
  - Statics and consts use their name (`constants-RISTRETTO_BASEPOINT_TABLE`).
  - The user: "let's keep the file names short".

### One function per patch

- Helpers the rewrite needs are **nested inside the patched function**, so that no patch depends
  on another. An early shared-helper patch was dropped for this reason.
- **Exception:** a closely connected change goes in the same patch. The Montgomery `Mul` patch
  inlines `Scalar::bits_le` and also deletes it, which avoids a dead-code warning and an
  `exclude` entry.
- A macro body counts as one function (`impl_basepoint_table!`'s `mul_base`).
- The patched code has no TODO or explanatory comments; the header carries the explanation.

### Body

- `git diff -W -- <file>`, run from the repository root, so the paths are
  `a/<crate>/src/<file>.rs`. `-W` shows the whole function, so an auditor sees the full context
  in the file. This needs `.gitattributes` with `*.rs diff=rust`.
- Run `rustfmt --edition <ed>` on the patched file before diffing.
- **Statics** have no function boundary: use plain short context.
- **Overlapping contexts:** when two patches touch neighbouring functions, their `-W` contexts
  overlap. Patches are applied one at a time, so each must still apply after the other. Trim the
  context lines at the boundary by hand and fix the `@@` line counts.

### Header

Free text before the first `diff --git` line (`git apply` ignores it):

```
Translation patch: <Rust item, e.g. <EdwardsPoint as Sum<T>>::sum>

Change: <one line: what the rewrite does>
Why: <the Aeneas limitation, with the issue number if known>
Behaviour: identical. | <exactly what differs>
Relies on: <a fact not visible in the diff>      (only when there is one)
```

- **Keep it minimal.** The user removed "Remove when …" lines and "none" entries and asked for
  "just the bare minimum of information".
- Where equivalence depends on code outside the diff, quote that code or state the fact under
  "Relies on". For example, the Montgomery header quotes the original `mul_bits_be` loop.

### Generating patches

1. Write each rewrite as a list of `(old_text, new_text)` replacements for one file.
2. Apply it to a clean `src/`, run `rustfmt`, then
   `git diff -W -- <file> > body.diff`, then restore `src/`.
3. Prepend the header.
4. To refresh a stale patch (wrong `index` blob, line offsets after an upstream merge): apply it,
   rediff, and re-add the header.

When starting from a branch that has workarounds edited directly into `src/`:
1. Split the branch's diff against the merge-base into hunks.
2. Group the hunks by enclosing function and drop comment-only lines.
3. Apply each group to a clean tree and rediff with `-W`.
4. Reset `src/` to upstream.

### Checks for every patch set

- Each patch applies **alone** (`git apply --check`).
- All patches apply and revert in forward and in reverse order, and `src/` is clean afterwards.
- `cargo test` (debug and release) passes with the patches applied, as do the tests of other
  feature sets and dependent crates.
- `cargo check` and `clippy` give no new warnings. The `fold` → `while let` patches produced
  clippy warnings that needed attention.

### Behaviour changes

Allowed only when the header declares them and the user agrees. Here:
- the `size_hint` dispatchers use actual lengths and consume their inputs eagerly. The user chose
  "patch with changed behaviour" over opaque;
- the Ristretto basepoint table became a copied static: same value, different address, ~30 KB
  more;
- `fold` → `while let Some(x) = it.next()` is identical only for lawful iterators;
- non-functional: some patches buffer secret data in `Vec`s without zeroizing it.

## 5. Patch review (independent audit)

The user's request: "dispatch several agents to very carefully check each patch file. it
should be possible to audit each patch file independently without knowing anything about the
rest of the code. the audit must confirm that the patch doesn't change any functionality."

### Setup

- Run several auditor agents in parallel (four here), each with a disjoint group of patches,
  grouped by Rust file or subsystem.
- Limit the number of agents to what memory allows.
- Agents are read-only on the repository: `git apply --check` only. Any test runs in a
  throwaway `git worktree add /tmp/audit-$RANDOM HEAD`, removed afterwards. No commits,
  checkouts, stashes or resets.

### Brief for each auditor

1. **Self-contained auditability.** Audit each patch by reading **only its file** first. Then
   list every fact needed that the file does not supply, verify it in the source, and report it
   as a "self-containedness gap" with suggested header text.
2. **Functional equivalence checklist:**
   - same return values;
   - same effects through `&mut`;
   - same panics (conditions and messages);
   - same order of observable calls (on caller-supplied iterators, `Borrow`, user trait impls);
   - same termination, including for infinite or unbounded inputs;
   - no new overflow, out-of-bounds or `unwrap` panics.

   Constant-time changes are flagged but are not counted as "functionality". Add points specific
   to the group, e.g. bit order and the skipped bit in a ladder, the seed and column order of a
   fold, `zip` polling order, `?` short-circuiting.
3. **Header accuracy.** Every declared difference is real and complete, and nothing undeclared
   changes.
4. **Evidence.** Where reasoning is not conclusive, run randomized differential tests of the old
   against the new function (e.g. 300 random scalars), plus clippy and release-mode tests.

### Output per patch

`### <file>`, then a verdict (EQUIVALENT / EQUIVALENT-AS-DECLARED / PROBLEM), the argument, the
gaps, and any header inaccuracies.

### Assembly and follow-up

1. Assemble the sections into one audit file with a summary table.
2. With the user's approval, rewrite the headers from the findings, citing only facts that were
   checked in the source.
3. Regenerate any patch found stale.
4. Re-run the apply/revert and test checks.

Here the result was 19 equivalent, 5 declared but incompletely, and 3 problems (the Ristretto
wrappers did not declare their own effect). Recurring findings:
- termination for infinite inputs was undeclared;
- the `fold` caveat;
- boilerplate "Behaviour" paragraphs;
- unjustified facts (length invariants, callee behaviour);
- zeroization of buffered secrets;
- two patches generated against a stale base.

The headers were then shortened at the user's request, keeping "Relies on" only where needed (12
of 27).

## 6. External items

- **Templates.** Aeneas writes `FunsExternal_Template.lean` and `TypesExternal_Template.lean`,
  which are gitignored. The hand-written `FunsExternal.lean` and `TypesExternal.lean` are never
  overwritten.
  - After each translation, diff them against the templates (a small script listing declarations
    present only in one of them).
  - Declarations span several lines, so grepping the line after `axiom` misses names: 36 stale
    axioms for functions that had since become translated were found this way.
- **Signatures are `opaque`** (the template prints `axiom`): "every function signature should be
  an opaque whenever possible". Behaviour is given by **spec axioms** that state the Rust
  documentation, marked `@[step]` where useful. Only spec axioms are trusted additions.
- **External crates get their own library**, e.g. `Subtle`, `Zeroize`:
  - **trusted part:** `Types.lean` (types only) and `Basic.lean` (`opaque` signatures with the
    template's names, plus one spec axiom per function);
  - **derived part:** `Lemmas.lean` (generic) and `Instances.lean` (about instances in
    `Funs.lean`), adding no axioms.

  Rules from the review of these libraries:
  1. opaque signature plus spec axiom, not a Lean model with a body;
  2. any type model must equal what Aeneas would generate if it translated that crate;
  3. trusted and derived parts separated, without duplication;
  4. a spec axiom that relies on trait-instance behaviour must be conditional on it, otherwise it
     can prove `False`;
  5. a verbatim body appears only where Aeneas's `impl_def` must unfold a default method
     (`@[trait_default]`).
- `FunsExternal.lean` imports only the libraries' `Basic` files.
- **Known limitation:** Aeneas generates every external crate's *traits* into the crate's own
  `Types.lean` (only its compiled-in `@[rust_trait]` table is skipped). So the trait-generic parts
  of these libraries depend on the translation. See `external-crate-traits.md`.

## 7. Several configurations in one translation (Charon multi-target)

Charon's `--targets` translates several targets and merges them. This also covers **feature
combinations**:
- **One target per configuration.** For each configuration, write a JSON target spec copied from
  the real triple:
  `"$(charon toolchain-path)/bin/rustc" -Z unstable-options --print target-spec-json --target <triple> > .llbc/<name>.json`.
  Pass `--targets $PWD/.llbc/<name>.json`, plus `-Zjson-target-spec -Zbuild-std=core,alloc`
  after `--`.
  - The spec file name becomes the target name.
  - Generate the specs at each run, never commit them, so they match the pinned nightly.
- **Per-configuration cfgs:** `export CARGO_TARGET_<NAME_UPPER>_RUSTFLAGS='--cfg feature="…" --cfg …'`
  (unset `CARGO_ENCODED_RUSTFLAGS`). Turning a feature on through `--cfg` is only valid when the
  feature has no dependencies (`precomputed-tables = []`).
- **Result:**
  - items identical on **all** targets appear once;
  - differing items get one variant per target, suffixed `.«<target>»`, plus an unsuffixed
    **façade** that dispatches on `get_target`;
  - items present only on some targets are kept only for those.
  - Here: {x86_64, i686} × {tables, no tables} = 4 targets, about 80 s.
- **Name the targets with hyphens** (`x86_64-tables`, `x86_64-no-tables`, `i686-tables`,
  `i686-no-tables`). Valid-identifier names (`x86_64`, `x86_64_no_tables`) caused **324**
  impl-name clashes, because Aeneas names a trait impl after the last path component of the type,
  which is then the target name.
- **Cost:** deduplication is all-or-nothing, so items that differ on any target get a variant on
  every target. `Funs.lean` grew from 47k to 65k lines.
- **For proofs:** shared items are proved once and each variant gets its own spec. Dispatcher
  specs case-split on the target, so they can wait until every variant is specified.

## 8. Catalogue: constructs that failed and their fix (Aeneas `nightly-2026.10.09`)

| Construct | Symptom | Fix |
|---|---|---|
| Iterator adapters: `map`, `zip`, `fold`, `collect`, `filter`, `skip`, `rev`, `by_ref`, `size_hint`, `chunks`, `all` | Lean: "`zip` is not a field of structure `core.iter.traits.iterator.Iterator`", "Unknown constant `…all`", "Unknown identifier `core.slice.Slice.chunks`" (the Lean library models only `next`, aeneas#1057) | Index loops, or `while let Some(x) = it.next()` |
| Loop over a generic `IntoIterator` parameter | Aeneas: "Could not find: type_var_id: 0 from ExtractBase.Item" | Nested helper `fn collect<It: Iterator>(mut it: It) -> Vec<It::Item>`, called with `.into_iter()` |
| `iter_mut().rev().zip(..)` borrows | Aeneas internal error (`InterpBorrowsCore.ml`) | Index loops |
| `collect::<Option<Vec<_>>>()?` | Lean: unknown `core.option.Option.Insts.CoreOpsTry_traitTry.branch` | Helper loop returning `None` early |
| Function pointer as argument (`map(T::from)`) | "Could not find: trait_impl_id" / "Unimplemented" | A closure |
| Local variable named like a module (`scalar`) | Lean: invalid field `Scalar` (aeneas#1098) | Rename it in the patch |
| `&raw const` pointer cast between `repr(transparent)` statics | "Unsupported operation: &raw const" | Build the value directly (copy), declared |
| `Debug` impls (`write!`, `Formatter`) | Aeneas internal error (`Interp.ml`) | exclude |
| Function returning `impl Iterator` | Adapters not modelled; a custom iterator type also fails (generated `Iterator` instance lists all provided methods) | Inline into the caller, delete the function in the same patch |
| `size_hint`-based dispatch | Not modellable | Patch with a declared behaviour change, or opaque |
| Huge constant tables | Lean "maximum recursion depth reached in the code generator" | Nothing needed: `Funs.lean` is a `noncomputable section`, so the definition silently becomes noncomputable. The user: "we are happy for everything to be non computable" |

Every upstream issue above is a reason to re-run the necessity check after an Aeneas update.

## 9. Pitfalls

- `git diff -W` without `*.rs diff=rust` → impl-sized, overlapping patches.
- Reverting several patches at once is not atomic → apply one by one, revert in reverse from an
  `EXIT` trap.
- Empty glob → `nullglob`.
- `CARGO_ENCODED_RUSTFLAGS` silently overrides `CARGO_TARGET_*_RUSTFLAGS`.
- A new Aeneas release changed its output format (`module` headers): the hand-written Lean files
  had to switch to `module` / `public import` / `@[expose] public section`.
- A new release can break an item that translated before; here, the `window.rs` `Debug` impl
  hit an internal error.
- A patch on an `opaque` function has no effect → run the necessity check.
- Lean stops after 100 errors → remove the limit to see the whole scope.
- A header copied from a similar patch carried wrong details → have the headers audited
  independently.
- Memory: elaborating the generated `Funs.lean` takes 5–6 GB. Run one Lean process per agent and
  few agents in parallel; agents must not use the Lean LSP.
- Aeneas's `toStr` uses `decide +native`, so string literals (e.g. `get_target` names) bring a
  native-evaluation axiom. `core.fmt.Formatter` is an `axiom` in the Aeneas library.
- Agents that `git rm` files leave staged deletions; tell agents not to commit, checkout, stash
  or reset.

## 10. Checklist for a new crate

1. Pin Aeneas to a release tag in `lakefile.toml`. Copy both scripts, `.gitattributes`, the
   `.gitignore` entries and the CI workflow, and adapt the names.
2. Add `[package.metadata.charon]` with `start_from` and empty `exclude`/`opaque`, plus the rule
   comments.
3. First translation; collect and group all Aeneas and Lean errors by Rust item.
4. Decide the scope per item with the user: exclude / opaque / patch.
5. Write one patch per function (`-W` body, minimal header). Iterate until translate,
   `lake build --wfail`, `cargo test` (debug and release), `cargo check`/clippy and a clean
   `src/` all pass.
6. Necessity check: every patch is needed.
7. Independent parallel audit of all patches, then fix the headers and regenerate stale patches.
8. Hand-write the External files: `opaque` signatures plus spec axioms. Put external crates in
   their own trusted `Types`/`Basic` libraries, with derived `Lemmas`/`Instances`.
9. Several configurations (features, word sizes): one JSON target spec each, hyphenated names.
10. Commit the generated output, then turn on CI (freshness check, `--wfail` build, linter on the
    hand-written libraries).
11. After each Aeneas release: re-translate, re-run the necessity check, diff the External files
    against the templates, and re-check that nothing new fails.
