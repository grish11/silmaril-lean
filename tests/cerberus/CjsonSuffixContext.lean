module
public meta import Silmaril.Elf.Corpus.CjsonSuffix.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.CjsonSuffix
/-- Complete record comparison for this domain's five exact allocations. The
key-set checks reject added/removed allocations before comparing every value. -/
private def sameMemory (a b : Mem.Concrete.State) : Bool :=
  let ids : List Int := [0,1,2,3,4]
  let keys := (Map.ofList (ids.map fun id => (id, ()))).keys
  a.enumTypes == b.enumTypes && a.nextId == b.nextId && a.lastAddress == b.lastAddress &&
  a.allocations.keys == keys && b.allocations.keys == keys &&
  ids.all (fun id => reprStr (a.allocations.lookup id) == reprStr (b.allocations.lookup id)) &&
  a.bytes == b.bytes && a.dead == b.dead && a.lastUsed == b.lastUsed &&
  a.pointerBytes == b.pointerBytes && a.functions == b.functions && a.stdout == b.stdout &&
  a.nextExcluded == b.nextExcluded && reprStr a.currentLocation == reprStr b.currentLocation
private def expectFailure (F : Silmaril.Project.Shapes.C.CFn Source.signature) (label : String) (readonly : Bool) (s : State) : IO Unit := do
  match (run F.file ∅ 100000 s).ending with
  | some (.defined _) => throw <| IO.userError s!"invalid {label} accepted"
  | none => throw <| IO.userError s!"invalid {label} exhausted fuel"
  | some ending =>
      match ending with
      | .ub _ .UB064_modifying_const =>
          unless readonly do throw <| IO.userError "missing allocation relabelled as readonly UB"
      | .unsupported why =>
          unless !readonly && why == "outside allocation lifetime UB mapping" do
            throw <| IO.userError s!"unexpected unsupported negative: {why}"
      | _ => throw <| IO.userError s!"wrong negative outcome: {(observation (some ending)).json.compress}"
      IO.println s!"PASS actual Core negative {label}: {(observation (some ending)).json.compress}"
public def main : IO Unit := do
  unless reprStr Source.Elaboration.core.funs == reprStr Source.programDocument.bindings.funs &&
      reprStr Source.Elaboration.core.funInfo == reprStr Source.programDocument.bindings.funInfo do
    throw <| IO.userError "actual source/Core/procedure metadata mismatch"
  let F := Source.Elaboration.function
  for input in List.finRange 4 do
    let before ← match Context.prepare input with
      | .ok s => pure s
      | .error why => throw <| IO.userError why
    let expected ← match Context.expectedMemory before.memory with
      | .ok memory => pure memory
      | .error why => throw <| IO.userError why
    let result := run F.file ∅ 100000 before
    match result.ending with
    | some (.defined _) => pure ()
    | ending => throw <| IO.userError s!"actual suffix_object {input}: {(observation ending).json.compress}"
    let after := {result.finalState.memory with currentLocation := expected.currentLocation}
    unless sameMemory after expected do
      throw <| IO.userError "actual Core differs from exact two typed-store complete-memory postcondition"
    -- These compare the entire source memory record, not just a permitted footprint.
    let unrelated := {after with bytes := after.bytes.insert (Context.heapAddress 2 + 24) (some 1)}
    unless !sameMemory unrelated expected do throw <| IO.userError "unrelated byte mutation hidden"
    let wrongProvenance := {after with pointerBytes := before.memory.pointerBytes}
    unless !sameMemory wrongProvenance expected do throw <| IO.userError "pointer-provenance mutation hidden"
    let wrongCounter := {after with nextExcluded := before.memory.nextExcluded}
    unless !sameMemory wrongCounter expected do throw <| IO.userError "excluded-action accounting mutation hidden"
    let changedLifetime := {after with dead := 4 :: after.dead}
    unless !sameMemory changedLifetime expected do throw <| IO.userError "caller lifetime mutation hidden"
    let changedOutput := {after with stdout := after.stdout ++ "unexpected"}
    unless !sameMemory changedOutput expected do throw <| IO.userError "stdout mutation hidden"
    let missingSecond := {after with bytes := before.memory.bytes, pointerBytes := before.memory.pointerBytes}
    unless !sameMemory missingSecond expected do throw <| IO.userError "missing heap stores hidden"
    if input.val == 0 then
      let noObject := {before with memory := {before.memory with allocations := before.memory.allocations.erase 2}}
      expectFailure F "missing receiver allocation (unsupported lifetime mapping remains labelled)" false noObject
      let some receiver := before.memory.allocations.lookup 2 | throw <| IO.userError "missing receiver"
      let readonly := {before with memory := {before.memory with allocations := before.memory.allocations.insert 2 ({receiver with readonly := some .UB064_modifying_const})}}
      expectFailure F "readonly receiver" true readonly
      let noParameter := {before with memory := {before.memory with allocations := before.memory.allocations.erase 0}}
      expectFailure F "missing parameter allocation" false noParameter
  IO.println "PASS four actual suffix_object Core executions: exact two typed pointer stores; complete unrelated memory/allocation/lifetime/provenance/stdout preservation; mutation/readonly/missing-allocation negatives; no contextual semantic proof"

/-- The actual observation predicate cannot hide changed stdout. This checks
its definition, not the C-to-ELF contextual claim. -/
example (before after expected : Mem.Concrete.State)
    (computed : Context.expectedMemory before = .ok expected)
    (changed : after.stdout ≠ expected.stdout) : ¬ Context.exactUpdate before after := by
  rintro ⟨actual, calculated, equal⟩
  have same : actual = expected := Except.ok.inj (calculated.symm.trans computed)
  subst actual
  have output := congrArg (fun memory : Mem.Concrete.State => memory.stdout) equal
  exact changed output
