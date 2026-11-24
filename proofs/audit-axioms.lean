import Lean.CoreM
import Lean.Util.CollectAxioms

open Lean

unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then
    throw <| IO.userError "usage: audit-axioms.lean MODULE ..."
  let modules := args.toArray.map String.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- Load private declarations too, including generated helpers and unused proofs.
  let env ← importModules (modules.map fun name => { module := name }) {}
    (loadExts := true) (level := .private)
  let checked ← Lean.Core.CoreM.toIO' (do
    let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
    let mut checked := 0
    for (name, _) in env.constants do
      if let some index := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[index]! then
          let unexpected := (← collectAxioms name).filter (!allowed.contains ·)
          unless unexpected.isEmpty do
            throwError "{name}: forbidden axioms {unexpected}"
          checked := checked + 1
    -- An import-only root can have no declarations of its own.
    pure checked)
    { fileName := "audit-axioms.lean", fileMap := default } { env := env }
  IO.println s!"Audited {checked} declarations in {modules.size} library modules"
