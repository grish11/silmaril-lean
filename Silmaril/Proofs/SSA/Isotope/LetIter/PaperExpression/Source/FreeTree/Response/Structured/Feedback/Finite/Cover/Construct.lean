module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Cover.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Mathlib.Basic.Finite.Prod

public section

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.CoverProofs

variable {Q K S T B : Code} {L : Table Q K S B} {R : Table Q K T B}
  {s₀ : S.Value} {t₀ : T.Value}

theorem run_eq_of_reach (obs : L.run s₀ = R.run t₀)
    {p : S.Value × T.Value} (reach : PairedReach L R s₀ t₀ p) :
    L.run p.1 = R.run p.2 := by
  induction reach with
  | initial => exact obs
  | after_reply _ r left right ih =>
      have next := (related_step ih).2 r
      rw [left, right] at next
      exact next

private theorem replies (obs : L.run s₀ = R.run t₀)
    {C : Code} (decode : C.Value ≃ {p // PairedReach L R s₀ t₀ p}) (v : C.Value) (r : K.Value) :
    ∃ result : B.Value ⊕ C.Value,
      Sum.map id (fun w => (decode w).val.1) result = L.reply (decode v).val.1 r ∧
      Sum.map id (fun w => (decode w).val.2) result = R.reply (decode v).val.2 r := by
  have next := (related_step (run_eq_of_reach obs (decode v).property)).2 r
  cases hl : L.reply (decode v).val.1 r <;> cases hr : R.reply (decode v).val.2 r <;> rw [hl, hr] at next
  · exact ⟨.inl _, rfl, congrArg Sum.inl next⟩
  · exact next.elim
  · exact next.elim
  · rename_i s t
    let pair : {p // PairedReach L R s₀ t₀ p} :=
      ⟨(s, t), .after_reply (decode v).property r hl hr⟩
    exact ⟨.inr (decode.symm pair), by simp [pair], by simp [pair]⟩

theorem exists_cover (obs : L.run s₀ = R.run t₀) : Nonempty (Cover L R s₀ t₀) := by
  let _ : _root_.Finite S.Value := finiteValue S
  let _ : _root_.Finite T.Value := finiteValue T
  obtain ⟨C, ⟨decode⟩⟩ := encodeFinite {p // PairedReach L R s₀ t₀ p} ⟨(s₀, t₀), .initial⟩
  let table : Table Q K C B :=
    ⟨fun v => L.request (decode v).val.1, fun v r => Classical.choose (replies obs decode v r)⟩
  exact ⟨⟨C, decode, table,
    fun v => ⟨rfl, fun r => (Classical.choose_spec (replies obs decode v r)).1⟩,
    fun v => ⟨(related_step (run_eq_of_reach obs (decode v).property)).1,
      fun r => (Classical.choose_spec (replies obs decode v r)).2⟩⟩⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.CoverProofs
