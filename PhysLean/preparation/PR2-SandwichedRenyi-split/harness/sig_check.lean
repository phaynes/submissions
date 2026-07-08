import QuantumInfo
/-!
Kernel signature dump for the PR2 move-refactor harness (Codex review B4).

WHY: source-identical text can elaborate to a DIFFERENT type if the ambient `variable` /
instance / universe / scoped-notation context differs between the old and new file. That
drift is invisible to source-text hashing, to `lake build`, and to `#print axioms`. This
dumps the fully-elaborated KERNEL type `Expr` (via `toString`, which is context-free) of
every name in `sig_names.txt`, one `NAME ⟪ <type> ⟫` record per line.

IMPORTANT (measured): the raw `toString` of a kernel type embeds *hygienic* binder names
that encode the SOURCE MODULE + a location hash, e.g.
  inst._@.QuantumInfo.Entropy.Relative.4004854524._hygCtx._hyg.6
When a declaration MOVES to a new module, only that cosmetic module-path/hash changes, not
the semantics — so the raw dump would false-positive on a clean move. The consumer
(`20_check.sh`) MUST normalize those away before hashing. This file emits the raw record;
`20_check.sh` applies the documented `sed` normalization:  s/_@\.[A-Za-z0-9_.]*_hyg[A-Za-z0-9._]*/_HYG_/g
so a pure move compares equal while genuine type/universe/implicit drift still differs.

Missing constants emit `NAME ⟪ MISSING ⟫` so a lost declaration is loud, not silent.

Usage (from a built physlib checkout, with sig_names.txt alongside):
  lake env lean --run sig_check.lean > sig.raw
  # then normalize+hash in 20_check.sh
-/
open Lean

def readNames : IO (Array Name) := do
  let raw ← IO.FS.readFile "sig_names.txt"
  let mut out := #[]
  for line in raw.splitOn "\n" do
    let s := line.trimAscii.toString
    if s.length > 0 && !s.startsWith "#" then
      out := out.push s.toName
  return out

def main : IO Unit := do
  let names ← readNames
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `QuantumInfo }] {} (trustLevel := 1024)
  for nm in names do
    match env.find? nm with
    | none    => IO.println s!"{nm} ⟪ MISSING ⟫"
    | some ci => IO.println s!"{nm} ⟪ {toString ci.type} ⟫"
