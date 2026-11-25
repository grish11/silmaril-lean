module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Defs
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Runtime (AdminInstr Value)
open Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded.Det

variable {I : Type} {S : Syntax I} (E : CoreEncoding S)

private theorem emit_read_one {a : AdminInstr I} {b : Admin}
    (h : emitAdmin E.emit a = some b) : readAdmin E.read b = some a := by
  cases a <;> simp [emitAdmin] at h
  · subst b; simp [readAdmin, E.read_emit]
  · subst b; rfl

theorem code_roundtrip {code : List (AdminInstr I)} (h : Admitted S code) :
    readCode E.read (emitCode E.emit code) = some code := by
  induction code with
  | nil => rfl
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := admitted_cons.mp h
    have emits : ∃ b, emitAdmin E.emit a = some b := by
      cases ha with
      | value v => exact ⟨_, E.value v⟩
      | divide t k => exact ⟨_, E.divide t k⟩
      | nop => exact ⟨_, E.nop⟩
      | trap => exact ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := emits
    have tailOk := ih ht
    simp only [readCode, emitCode, List.filterMap_cons, hb, List.mapM_cons, emit_read_one E hb]
    change (readCode E.read (emitCode E.emit tail)).bind (fun xs => some (a :: xs)) = _
    rw [tailOk]
    rfl

@[simp] private theorem emit_values (vs : List Value) :
    emitCode E.emit (S.values vs) = vals (vs.map liftValue) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simpa only [Syntax.values, List.map_cons, emitCode, List.filterMap_cons, E.value, vals] using
      congrArg (List.cons (liftValue v).toAdmin) ih

private theorem emit_append (xs ys : List (AdminInstr I)) :
    emitCode E.emit (xs ++ ys) = emitCode E.emit xs ++ emitCode E.emit ys :=
  List.filterMap_append

private theorem emit_trap : emitCode E.emit [.trap] = [.trap] := rfl

private theorem trap_context {H : Type} {P : Profile} (s : Store H) (f : Frame)
    (vs : List Value) (tail : List (AdminInstr I)) (hne : vs ≠ [] ∨ emitCode E.emit tail ≠ []) :
    Step P noHost ⟨s, f, emitCode E.emit (S.values vs ++ [.trap] ++ tail)⟩ ⟨s, f, [.trap]⟩ := by
  have expanded : emitCode E.emit (S.values vs ++ [.trap] ++ tail) =
      vals (vs.map liftValue) ++ [.trap] ++ emitCode E.emit tail := by
    rw [emit_append, emit_append, emit_values, emit_trap]
  rw [expanded]
  exact .trapInstrs (by simpa using hne)

private theorem redex_to_core {H : Type} {P : Profile} (s : Store H) (f : Frame)
    {before after : List (AdminInstr I)} (h : Redex S before after) :
    Step P noHost ⟨s, f, emitCode E.emit before⟩ ⟨s, f, emitCode E.emit after⟩ := by
  cases h with
  | divide t k x y z ok =>
    simpa only [emitCode, List.filterMap_cons, List.filterMap_nil, E.value, E.divide, liftValue, Value.int, Val.toAdmin, Division.divOp] using
      (Step.numeric (P := P) (host := noHost) (s := s) (f := f) (.intBinOp ok))
  | divTrap t k x y cause trap =>
    rw [emit_trap]
    simpa only [emitCode, List.filterMap_cons, List.filterMap_nil, E.value, E.divide, liftValue,
      Value.int, Val.toAdmin, Division.divOp] using (Step.numeric (P := P) (host := noHost) (s := s) (f := f) (.intBinOpTrap trap))
  | nop =>
    simpa only [emitCode, List.filterMap_cons, List.filterMap_nil, E.nop] using
      (Step.parametric (P := P) (host := noHost) (s := s) (f := f) .nop)
  | trapValues v vs tail _ => exact trap_context E s f (v :: vs) tail (.inl (by simp))
  | trapTail a tail admitted =>
    have hne : emitCode E.emit (a :: tail) ≠ [] := by
      intro he
      have he' := code_roundtrip E admitted
      simp [he, readCode] at he'
    exact trap_context E s f [] (a :: tail) (.inr hne)

theorem step_to_core {H : Type} {P : Profile} (s : Store H) (f : Frame)
    {before after : List (AdminInstr I)} (h : DerivesEdge S before after) :
    Step P noHost ⟨s, f, emitCode E.emit before⟩ ⟨s, f, emitCode E.emit after⟩ := by
  apply derives_induction (R := fun a b =>
    Step P noHost ⟨s, f, emitCode E.emit a⟩ ⟨s, f, emitCode E.emit b⟩) _ _ h
  · exact redex_to_core E s f
  · intro saved before after tail middle _
    have inContext := lift_instrs (saved.map liftValue) (emitCode E.emit tail) _ _ middle
    rw [← emit_values E saved] at inContext
    simpa [emitCode, List.filterMap_append] using inContext

end Silmaril.Wasm.Institution.Operational.LegacyDivision.Proofs
