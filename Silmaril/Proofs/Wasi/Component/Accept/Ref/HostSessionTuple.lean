module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Examples
public import Silmaril.Wasi.Component.Accept.Consequence.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs
public import Silmaril.Wasm.Component.Reference.HAcceptTuple.Defs

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.HostSession.Examples`: the IR lowering of
`tupleHiBytes` is `HAcceptTuple.tupleI.toComp` with its core module carried as bytes that decode
to `tupleCore`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSessionTuple

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HAcceptTuple
open Silmaril.Wasm.Component.Reference.LinkedSession (unitTy)

/-- The function of `tupleCore`: `i32.const 104; i32.const 105; call 0` at type `1`. -/
def isTupleFunc : List (Silmaril.Wasm.Func) → Bool
  | [⟨t, [], [.intConst .i32 a, .intConst .i32 b, .call x]⟩] =>
    t == ⟨1⟩ && a == 104 && b == 105 && x == ⟨0⟩
  | _ => false

/-- A module equal to `tupleCore`, field by field. -/
def isTupleCore (m : Silmaril.Wasm.Module) : Bool :=
  m.types == tupleCore.types && m.imports == tupleCore.imports && m.tags.isEmpty &&
    m.globals.isEmpty && m.memories.isEmpty && m.tables.isEmpty && isTupleFunc m.funcs &&
    m.data.isEmpty && m.elems.isEmpty && m.start == none && m.exports == tupleCore.exports

theorem isTupleFunc_eq {fs : List Silmaril.Wasm.Func} (h : isTupleFunc fs = true) :
    fs = tupleCore.funcs := by
  unfold isTupleFunc at h
  split at h
  next t a b x =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    rfl
  next => cases h

theorem isTupleCore_eq {m : Silmaril.Wasm.Module} (h : isTupleCore m = true) : m = tupleCore := by
  obtain ⟨types, imports, tags, globals, memories, tables, funcs, data, elems, start, exports⟩ := m
  simp only [isTupleCore, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hf⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rw [isTupleFunc_eq hf]
  rfl

/-- The lowered component is `tupleI.toComp` with its module as a `CoreMod` decoding to
`tupleCore`, with `tupleI.mod`'s interface. -/
def isTupleLowered : Option (Comp Binary.CoreMod) → Bool
  | some (.mk I [.core cm [⟨[.lower ft], .call 0⟩]] [⟨"run", ft', ⟨[.lift ft''], .call 1⟩⟩]) =>
    I == tupleI.imports && ft == acceptTy && ft' == unitTy && ft'' == unitTy &&
      CoreModule.imports cm == tupleI.mod.imports && CoreModule.exports cm == tupleI.mod.exports &&
      ((Silmaril.Wasm.Binary.Core.decode? cm.bytes).map isTupleCore == some true)
  | _ => false

theorem isTupleLowered_tupleHi :
    isTupleLowered (Silmaril.Wasi.Accept.ComponentAcceptor.decodeBinary
      Silmaril.Wasi.Accept.Ref.Examples.tupleHiBytes) = true := by
  decide +kernel

theorem lowered_eq {o : Option (Comp Binary.CoreMod)} (h : isTupleLowered o = true) :
    ∃ cm : Binary.CoreMod,
      o = some (.mk tupleI.imports [.core cm (SimpleI.lowerArgs tupleI.imports)]
        tupleI.toComp.exports) ∧
      CoreModule.imports cm = tupleI.mod.imports ∧ CoreModule.exports cm = tupleI.mod.exports ∧
      Binary.coreModule cm = tupleCore := by
  unfold isTupleLowered at h
  split at h
  next I cm ft ft' ft'' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hi⟩, he⟩, hd⟩ := h
    obtain ⟨m, hm, hmt⟩ := Option.map_eq_some_iff.mp hd
    refine ⟨cm, rfl, hi, he, ?_⟩
    simp only [Binary.coreModule, hm, isTupleCore_eq hmt, Option.getD_some]
  next => cases h

/-- **The IR lowering of `tupleHiBytes`.** -/
theorem decodeBinary_tupleHi :
    ∃ cm : Binary.CoreMod,
      Silmaril.Wasi.Accept.ComponentAcceptor.decodeBinary
          Silmaril.Wasi.Accept.Ref.Examples.tupleHiBytes =
        some (.mk tupleI.imports [.core cm (SimpleI.lowerArgs tupleI.imports)]
          tupleI.toComp.exports) ∧
      CoreModule.imports cm = tupleI.mod.imports ∧ CoreModule.exports cm = tupleI.mod.exports ∧
      Binary.coreModule cm = tupleCore :=
  lowered_eq isTupleLowered_tupleHi

end Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSessionTuple
