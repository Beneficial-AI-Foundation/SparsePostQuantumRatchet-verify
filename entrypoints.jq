# Usage: jq -r [--arg status all|verified|unverified] [--arg callers rust|any] -f entrypoints.jq FILE
# Defaults: status=all, callers=rust.
# Rust exec atoms (non-stub, non-test) that no caller depends on, filtered by status.
# The status filter applies to the output only, so all = verified + unverified.
# callers=rust: only non-test Rust exec atoms count as callers.
# callers=any:  every non-test, non-blueprint atom counts as a caller (Lean too).
($ARGS.named.status // "all") as $status
| ($ARGS.named.callers // "rust") as $callers
|
def is_test: ((.["code-module"]//"")|test("test")) or ((.["display-name"]//"")|test("test"));
def is_stub: .["code-path"]=="" and .["code-text"]["lines-start"]==0 and .["code-text"]["lines-end"]==0;
def is_verified: (.["verification-status"] // "") | IN("verified","transitively-verified");
def has_status: if $status=="verified" then is_verified
                elif $status=="unverified" then (is_verified|not)
                else true end;
def rust_exec: .language=="rust" and .kind=="exec" and (is_test|not);
def caller: if $callers=="any" then (is_test|not) and .language!="blueprint" else rust_exec end;
.data as $d
| ([$d[] | select(caller) | .dependencies[]?] | unique) as $deps
| $d | to_entries[]
| select((.value|rust_exec) and (.value|is_stub|not) and (.value|has_status))
| select(.key as $k | $deps | bsearch($k) < 0)
| "\(.value["verification-status"] // "-")\t\(.key)"
