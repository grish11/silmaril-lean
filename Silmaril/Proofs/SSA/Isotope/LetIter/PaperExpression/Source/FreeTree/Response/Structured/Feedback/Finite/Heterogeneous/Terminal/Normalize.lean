module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Iteration

public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.LocallyNameless

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

variable {count : Nat} {F : Family count} {S B : Code} {ε : Type}
  [HasEff (Opcode F) ε] {pe : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "H" => HasType Ops Free
local notation "E" => AbortEquiv (Φ := Ops) pe Free
local notation "C" => Code.sum B S
local notation "J" => Code.sum (Code.sum B S) S

private def stageReply (M : Table F S B) : B.Value ⊕ S.Value → (Code.sum B S).Value ⊕ S.Value
  | .inl b => .inl (.inl b)
  | .inr t =>
    match M t with
    | .ret _ => .inr t
    | .call .. => .inl (.inr t)

/-- In a nested iteration, use the inner repeat only for immediate-return
targets. Yield all other repeats to the outer iterator. -/
private def stage (M : Table F S B) : Table F S (Code.sum B S) := fun s =>
  match M s with
  | .ret v => .ret (.inl v)
  | .call f x k => .call f x (fun r => stageReply M (k r))

omit [HasEff (Opcode F) ε] in
private theorem flatten_typed : H (.snoc .nil (J).ty) (flattenHandler Ops) (C).ty :=
  .case .bv .bv (.inr .bv)

private theorem flatten_left (v : (C).Value) :
    E .nil (plug (flattenHandler Ops) (nativeValue Ops J (.inl v))) (nativeValue Ops C v) (C).ty :=
  handler_left (l := .bv 0) (r := .inr (.bv 0)) rfl .bv (.inr .bv) v

private theorem flatten_right (v : S.Value) :
    E .nil (plug (flattenHandler Ops) (nativeValue Ops J (.inr v))) (nativeValue Ops C (.inr v)) (C).ty :=
  handler_right (l := .bv 0) (r := .inr (.bv 0)) rfl .bv (.inr .bv) v

private theorem flatten_stage_reply (M : Table F S B) (v : (C).Value) :
    E .nil (plug (flattenHandler Ops) (nativeValue Ops J (stageReply M v))) (nativeValue Ops C v) (C).ty := by
  cases v with
  | inl a => exact flatten_left (.inl a)
  | inr s =>
    cases row : M s with
    | ret _ => simpa only [stageReply, row] using (flatten_right (F := F) (B := B) (pe := pe) s)
    | call _ _ _ =>
      simpa only [stageReply, row] using (flatten_left (F := F) (B := B) (pe := pe) (.inr s))

private theorem flatten_stage (M : Table F S B) :
    E (.snoc .nil S.ty) (.case (nativeBody (stage M)) (.bv 0) (.inr (.bv 0))) (nativeBody M) (C).ty := by
  have ht := body_typed (stage M)
  have bind := Equiv.bindCase (pureEff := pe) ht
    (show H (.snoc (.snoc .nil S.ty) (C).ty) (.bv 0) (C).ty from .bv)
    (show H (.snoc (.snoc .nil S.ty) S.ty) (.inr (.bv 0)) (C).ty from .inr .bv)
  change LocallyNameless.Equiv pe Free _ _ (.let₁ (nativeBody (stage M)) (flattenHandler Ops).underBinder) _ at bind
  refine (Refinement.equiv bind).trans (by_values S (.let₁ ht flatten_typed.underBinder) (body_typed M) (fun s => ?_))
  rw [plug_bind]
  refine (Refinement.let₁ (body_beta (stage M) s) (.refl flatten_typed)).trans
    (Refinement.trans ?_ (body_beta M s).symm)
  cases row : M s with
  | ret v =>
    simp only [stage, row, nativeRow]
    exact (bind_value flatten_typed (.inl (.inl v))).trans (flatten_left (.inl v))
  | call f x k =>
    simp only [stage, row]
    exact bind_call x (fun r => stageReply M (k r)) k flatten_typed (fun r => flatten_stage_reply M (k r))

private theorem handle_stage_reply (M : Table F S B) (v : (C).Value) :
    E .nil (plug (loopHandler (nativeBody (stage M))) (nativeValue Ops J (stageReply M v)))
      (nativeValue Ops C (M.contractReply v)) (C).ty := by
  cases v with
  | inl b => exact loopHandler_left (body_typed (stage M)) (.inl b)
  | inr s =>
    cases row : M s with
    | ret b =>
      have terminal : (stage M) s = .ret (.inl b) := by simp [stage, row]
      simpa only [stageReply, Table.contractReply, row] using
        (loopHandler_right (pe := pe) (body_typed (stage M)) s).trans (loop_return (stage M) s terminal)
    | call _ _ _ =>
      simpa only [stageReply, Table.contractReply, row] using
        (loopHandler_left (pe := pe) (body_typed (stage M)) (.inr s))

private theorem inner_at_value (M : Table F S B) (s : S.Value) :
    E .nil (.iter (nativeValue Ops S s) (nativeBody (stage M)))
      (plug (nativeBody M.contract) (nativeValue Ops S s)) (C).ty := by
  let hb := body_typed (stage M)
  have handler := loopHandler_typed hb
  refine (unfold_closed hb s).trans ((Refinement.let₁ (body_beta (stage M) s) (.refl handler)).trans ?_)
  refine Refinement.trans ?_ (body_beta M.contract s).symm
  cases row : M s with
  | ret v =>
    simp only [stage, Table.contract, row, nativeRow]
    exact (bind_value handler (.inl (.inl v))).trans (loopHandler_left hb (.inl v))
  | call f x k =>
    simp only [stage, Table.contract, row]
    exact bind_call x (fun r => stageReply M (k r)) (fun r => M.contractReply (k r))
      handler (fun r => handle_stage_reply M (k r))

private theorem inner_stage (M : Table F S B) :
    E (.snoc .nil S.ty) (.iter (.bv 0) (nativeBody (stage M)).underBinder) (nativeBody M.contract) (C).ty := by
  have hb := body_typed (stage M)
  refine by_values S (.iter .bv hb.underBinder) (body_typed M.contract) (fun s => ?_)
  change E .nil (plug (.iter (.bv 0) (nativeBody (stage M)).underBinder) (nativeValue Ops S s)) _ _
  have eq : (nativeBody (stage M)).underBinder = widen (nativeBody (stage M)) 1 := by
    conv_lhs => rw [← widen_zero (nativeBody (stage M)), widen_under]
  rw [eq]
  change E .nil (plug (loopArm (nativeBody (stage M)) 0) (nativeValue Ops S s)) _ _
  rw [loopArm_plug]
  exact inner_at_value (pe := pe) M s

theorem contract_native (M : Table F S B) (s : S.Value) :
    E .nil (.iter (nativeValue Ops S s) (nativeBody M)) (.iter (nativeValue Ops S s) (nativeBody M.contract)) B.ty := by
  have ha := value_typed S s (Φ := Ops) .nil
  have diagonal := Equiv.codiagonal (pureEff := pe) ha (body_typed (stage M))
  exact (AbortEquiv.symm (Refinement.iter (.refl ha) (flatten_stage (pe := pe) M))).trans
    ((Refinement.equiv diagonal.symm).trans (Refinement.iter (.refl ha) (inner_stage M)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
