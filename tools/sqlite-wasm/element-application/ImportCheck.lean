module

import SqliteWasm.ElementApplication

open Silmaril.Wasm Silmaril.Wasm.Execution.Core SqliteWasm

example {H : Type} {s : Store H} {f : Frame} {m : Module}
    {tableAddr elemAddr : Nat} {table : TableInst} {elem : ElemInst}
    (decode : Binary.Core.decode? originalBytes.toByteArray = some m)
    (tableEntry : s.table? f ⟨0⟩ = some (tableAddr, table))
    (elemEntry : s.elem? f ⟨0⟩ = some (elemAddr, elem))
    (destination : 343 ≤ table.refs.length) (source : elem.refs.length = 342) :
    initElem? evalConst? s f m =
      some (((s.setTable tableAddr
        { table with refs := table.refs.take 1 ++ elem.refs ++ table.refs.drop 343 }).setElem elemAddr []), f) := by
  have pinned : m = sqlite := Option.some.inj (decode.symm.trans originalDecode)
  subst m
  exact reactorElementPhase tableEntry elemEntry destination source

example : sqlite.tables.map (fun t => (t.type.address, t.type.limits.min.val)) = [(.i32, 343)] :=
  reactorTableMinimum

#print axioms reactorElementSegmentMode
#print axioms reactorElementSegmentLength
#print axioms reactorTableMinimum
#print axioms reactorElementSegmentApplied
#print axioms reactorElementPhase
