module

public import Lean.Util.CollectAxioms
public import Lean.Elab.Command

@[expose] public section
set_option backward.privateInPublic true


/-! Executable axiom-audit support. This contains no mathematical assertions.
It is compiled separately so that elaborating an inline `run_cmd` over the
entire project's environment does not recompile the auditing procedure.
-/

open Lean Elab Command

namespace UnitDistanceAudit

/-- Audit every declaration from modules or namespaces with the supplied
dot-separated `Name` prefix, including private auxiliaries. This is not a
string prefix: `Foo.Batch` does not select the module `Foo.Batch01`.
An empty selection is an error. The standard Lean 4.32
collector reads complete transitive axiom closures cached in imported modules.
Independent kernel replay remains a separate verification step. -/
def audit (project : Name) : CommandElabM Unit := do
  liftIO <| IO.eprintln "Axiom audit: starting environment selection."
  liftIO <| (← IO.getStderr).flush
  let env ← getEnv
  -- Cache the kernel environment and its maps once. The convenience
  -- environment accessors rebuild the kernel view from asynchronous
  -- elaboration state; invoking them for every imported name is costly.
  let kernelEnv := env.toKernelEnv
  let ownership := kernelEnv.const2ModIdx
  let modules := env.header.moduleNames
  let names := kernelEnv.constants.fold (init := #[]) fun acc name _ =>
    let owned := match ownership[name]? with
      | some idx => match modules[idx.toNat]? with
        | some mod => project.isPrefixOf mod
        | none => false
      | none => false
    if owned || project.isPrefixOf name then acc.push name else acc
  liftIO <| IO.eprintln s!"Axiom audit: {names.size} project declarations selected."
  liftIO <| (← IO.getStderr).flush
  if names.isEmpty then
    throwError "Axiom audit: no declarations matched {project}. Select an existing module or namespace; Name prefixes match dot-separated components, not partial filenames."
  let permitted : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut all : NameSet := {}
  let mut audited : Nat := 0
  for name in names do
    if audited < 3 then
      liftIO <| IO.eprintln s!"Axiom audit: beginning {name}."
    unless (kernelEnv.find? name).isSome do
      throwError "Missing checked project declaration {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Forbidden axiom {axiomName}, reached from project declaration {name}"
      all := all.insert axiomName
    audited := audited + 1
    if audited % 500 == 0 then
      liftIO <| IO.eprintln s!"Axiom audit: {audited}/{names.size} complete transitive axiom closures checked."
      liftIO <| (← IO.getStderr).flush
  logInfo m!"Audited all {names.size} project declarations (including private auxiliaries and attributed ports); their complete transitive axiom union is {all.toArray}."


end UnitDistanceAudit
