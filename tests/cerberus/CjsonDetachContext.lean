module
public meta import Silmaril.Elf.Corpus.CjsonDetach.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.CjsonDetach
private def sample (seed : Fin 16) : Context.Input where
  address j := 1048576 + 4096 * seed.val + 128 * j.val
  payload j k := BitVec.ofNat 8 (seed.val * 17 + j.val * 31 + k.val)
  aligned := by intro j; omega
  lower := by intro j; omega
  upper := by intro j; change 1048576 + 4096 * seed.val + 128 * j.val + 64 < 140737488355328; omega
  disjoint := by intro j k neq; have h : j.val ≠ k.val := fun e => neq (Fin.ext e); omega
/-- Complete record comparison for this domain's five exact allocations. The
key-set checks reject added/removed allocations before comparing every value. -/
private def sameMemory (a b : Mem.Concrete.State) : Bool :=
  let ids : List Int := [0,1,2,3,4,5,6]
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
  for seed in List.finRange 16 do
    let input := sample seed
    let before ← match Context.prepare input with
      | .ok state => pure state
      | .error why => throw <| IO.userError why
    let expected ← match Context.expectedMemory input before.memory with
      | .ok memory => pure memory
      | .error why => throw <| IO.userError why
    let result := run F.file ∅ 400000 before
    match result.ending with
    | some (.defined (.loaded (.specified (.pointer (.allocated 4 returned))))) =>
        unless returned == input.address 2 do throw <| IO.userError "wrong pointer return address"
    | ending => throw <| IO.userError s!"actual detach: {(observation ending).json.compress}"
    let after := {result.finalState.memory with currentLocation := expected.currentLocation}
    unless sameMemory after expected do
      IO.println s!"lastUsed actual={after.lastUsed} expected={expected.lastUsed}; excluded actual={after.nextExcluded} expected={expected.nextExcluded}"
      throw <| IO.userError "actual Core differs from exact complete-memory four-store postcondition"
    let some (some previous) := after.bytes.lookup (input.address 4 + 24 : Int)
      | throw <| IO.userError "missing unrelated byte"
    let unrelated := {after with bytes := after.bytes.insert (input.address 4 + 24) (some ((previous+1)%256))}
    let noStores := {after with bytes := before.memory.bytes, pointerBytes := before.memory.pointerBytes}
    let noProvenance := {after with pointerBytes := before.memory.pointerBytes}
    let dead := {after with dead := 4 :: after.dead}
    let output := {after with stdout := "unexpected"}
    unless !sameMemory unrelated expected && !sameMemory noStores expected &&
        !sameMemory noProvenance expected && !sameMemory dead expected && !sameMemory output expected do
      throw <| IO.userError "complete memory negative failed"
    for (j, offset) in [(1,0),(3,8),(2,8),(2,0)] do
      let start := input.address j + offset
      let missing := {after with bytes := (List.range 8).foldl (fun bytes k =>
        match before.memory.bytes.lookup (start+k : Int) with
        | some byte => bytes.insert (start+k) byte
        | none => bytes.erase (start+k)) after.bytes}
      unless !sameMemory missing expected do throw <| IO.userError "omitted individual source store hidden"
    if seed.val == 0 then
      let some receiver := before.memory.allocations.lookup 3 | throw <| IO.userError "missing predecessor"
      let readonly := {before with memory := {before.memory with allocations := before.memory.allocations.insert 3 ({receiver with readonly := some .UB064_modifying_const})}}
      expectFailure F "readonly predecessor" true readonly
      let missing := {before with memory := {before.memory with allocations := before.memory.allocations.erase 4}}
      expectFailure F "missing item allocation" false missing
    IO.println s!"PASS actual Core detachment seed={seed.val}: pointer return, four exact typed stores, complete memory and mutation negatives"
  IO.println "Observations only; generalized contextual obligation remains UNPROVED"

/-- Definition check only: the actual observation excludes ONLY the diagnostic
location, so an unrelated stdout mutation cannot satisfy the exact update. -/
example (input : Context.Input) (before after expected : Mem.Concrete.State)
    (computed : Context.expectedMemory input before = .ok expected)
    (changed : after.stdout ≠ expected.stdout) : ¬ Context.exactUpdate input before after := by
  rintro ⟨actual, calculated, equal⟩
  have same : actual = expected := Except.ok.inj (calculated.symm.trans computed)
  subst actual
  have output := congrArg (fun memory : Mem.Concrete.State => memory.stdout) equal
  exact changed output

-- A numerically equal return pointer carrying the predecessor's allocation ID
-- cannot satisfy the actual return observation. This is a definition check.
example (input : Context.Input) :
    ¬ Context.returnMatches input (.loaded (.specified (.pointer (.allocated 3 (input.address 2))))) := by
  simp [Context.returnMatches]
