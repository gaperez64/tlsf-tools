import Lean.CoreM
import Lean.Util.CollectAxioms
import Lean.Util.Path

open Lean

unsafe def main (args : List String) : IO Unit := do
  let [root] := args | throw <| IO.userError "usage: audit-axioms.lean LIBRARY"
  let directory := System.FilePath.mk root
  let paths ← if ← directory.isDir then directory.walkDir else pure #[]
  let mut modules := #[]
  for path in paths.push (directory.withExtension "lean") do
    if path.extension == some "lean" && (← path.pathExists) then
      modules := modules.push <|
        (path.withExtension "").components.foldl Name.str .anonymous
  if modules.isEmpty then
    throw <| IO.userError s!"no library modules found for {root}"
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
    if checked == 0 then
      throwError "no library declarations audited"
    pure checked)
    { fileName := "audit-axioms.lean", fileMap := default } { env := env }
  IO.println s!"Audited {checked} declarations in {modules.size} library modules"
