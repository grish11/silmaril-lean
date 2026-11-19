module
public meta import Silmaril.Elf.Corpus.CjsonInsert.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.CjsonInsert
public def main : IO Unit := do
  for hseed : seed in List.range 4 do
    for append in [false,true] do
      let i : Context.Input := {
        append := append, base := 1048576+65536*seed
        payload := fun off => BitVec.ofNat 8 (off*31+seed*17)
        aligned := by omega
        lower := by omega
        upper := by have : seed < 4 := List.mem_range.mp hseed; omega }
      let before ← match Context.prepare i with | .ok s => pure s | .error e => throw <| IO.userError e
      let expected ← match Context.expectedMemory i before.memory with | .ok m => pure m | .error e => throw <| IO.userError e
      let result := run Source.Elaboration.function.file ∅ 2000000 before
      match result.ending with
      | some (.defined (.loaded (.specified (.integer n)))) =>
        unless n == 1 do throw <| IO.userError "actual insertion integer result mismatch"
      | _ => throw <| IO.userError s!"actual insertion failed:{(observation result.ending).json.compress}"
      let after := result.finalState.memory
      unless after.enumTypes == before.memory.enumTypes && after.functions == before.memory.functions && after.stdout == before.memory.stdout do
        throw <| IO.userError "caller registration/stdout changed"
      for id in List.range 9 do
        unless reprStr (after.allocations.lookup (Int.ofNat id)) == reprStr (before.memory.allocations.lookup (Int.ofNat id)) &&
            after.dead.contains (Int.ofNat id) == before.memory.dead.contains (Int.ofNat id) do
          throw <| IO.userError "caller metadata/lifetime changed"
      for a in (List.range 384).map (i.base+·) ++ (List.range 24).map (4096+·) do
        unless after.bytes.lookup (Int.ofNat a) == expected.bytes.lookup (Int.ofNat a) &&
            after.pointerBytes.lookup (Int.ofNat a) == expected.pointerBytes.lookup (Int.ofNat a) do
          throw <| IO.userError "exact caller byte/provenance updates differ"
      for id in List.range after.nextId.toNat do
        if (id : Int) >= before.memory.nextId then
          unless after.dead.contains (Int.ofNat id) do throw <| IO.userError "private automatic object escaped cleanup"
      if seed == 0 && !append then
        let some allocation := before.memory.allocations.lookup 7 | throw <| IO.userError "new caller item missing"
        let readonly := {before with memory := {before.memory with allocations := before.memory.allocations.insert 7 {allocation with readonly := some .UB064_modifying_const}}}
        match (run Source.Elaboration.function.file ∅ 2000000 readonly).ending with
        | some (.ub _ .UB064_modifying_const) => pure ()
        | _ => throw <| IO.userError "readonly actual source mutation accepted"
        let missing := {before with memory := {before.memory with allocations := before.memory.allocations.erase 7}}
        match (run Source.Elaboration.function.file ∅ 2000000 missing).ending with
        | some (.unsupported why) =>
          unless why == "outside allocation lifetime UB mapping" do throw <| IO.userError why
        | _ => throw <| IO.userError "missing caller allocation negative mismatch"
  IO.println "PASS8 actual insertion Core context executions: exact four/interior or three/append pointer stores, caller bytes/provenance/metadata/lifetimes/stdout, actual private cleanup, readonly/missing-allocation negatives. Finite observations only; observation adequacy and semantic refinement remain unproved."
