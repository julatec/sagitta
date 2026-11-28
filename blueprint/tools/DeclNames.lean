/-
Prints the name of every declaration of this repository's own libraries (the vendored ones
included), one per line, sorted.

`blueprint/tools/check_names.sh --list FILE` uses the list to check the `\lean{...}` names of the
blueprint without loading Lean, which is useful while writing a chapter. The script makes the
list itself (`check_names.sh --make-list`, after `lake build`); by hand, from the root of the
repository, with the roots of the libraries of `lakefile.toml` as arguments:

    lake env lean --run blueprint/tools/DeclNames.lean Sagitta Sagitta.Map ... > blueprint/decl_names.txt

It imports the given modules, as `checkdecls` imports the roots of every library, and keeps the
declarations whose module has the same first component as one of them (`Sagitta`, `Cslib`,
`CslibFrontier`). Declarations of Mathlib, Lean and the other dependencies are left out: a
`\lean{...}` that cites one of them is only checked by the full check. Internal names (auxiliary
definitions that Lean generates, private names) are left out as well.
-/
import Lean
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run blueprint/tools/DeclNames.lean MODULE..."
    return 1
  let roots : Array Name := args.toArray.map String.toName
  let ours : Array Name := roots.map Name.getRoot
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (roots.map fun module => { module }) {}
  let modules := env.header.moduleNames
  let mut names : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    let some idx := env.getModuleIdxFor? n | continue
    if ours.contains modules[idx.toNat]!.getRoot then
      names := names.push n.toString
  for s in names.qsort (· < ·) do
    IO.println s
  return 0
