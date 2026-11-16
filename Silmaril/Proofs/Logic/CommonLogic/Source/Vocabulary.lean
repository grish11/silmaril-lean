module

public import Silmaril.Logic.CommonLogic.Source.Vocabulary.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source
open CategoryTheory

theorem find?_append_of_some {α : Type} (x : String) (a b : List (String × α))
    (v : α) (h : find? x a = some v) : find? x (a ++ b) = some v := by
  induction a with
  | nil => simp [find?] at h
  | cons p ps ih =>
      simp only [find?] at h
      simp only [List.cons_append, find?]
      split at h <;> simp_all

theorem Expr.elaborate_supports {S T : Core.Signature} {a : Names S} {b : Names T}
    {f : S ⟶ T} (h : a.Supports b f) {kind : Core.Kind} (raw : Expr kind)
    (ι κ : List String) (typed : Core.Expr S ι.length κ.length kind)
    (decoded : raw.elaborate a ι κ = some typed) :
    raw.elaborate b ι κ = some (typed.map f) := by
  induction raw with
  | individual x =>
      cases hi : index? x ι with
      | some i =>
          simp only [elaborate, hi, Option.some.injEq] at decoded
          subst typed
          simp only [elaborate, hi, Core.Expr.map]
      | none =>
          cases hd : find? x a.discourse with
          | none => simp [elaborate, hi, hd] at decoded
          | some d =>
              simp only [elaborate, hi, hd, Option.map_some, Option.some.injEq] at decoded
              subst typed
              simp only [elaborate, hi, h.discourse x d hd, Option.map_some, Core.Expr.map]
  | reference x =>
      cases hi : index? x ι with
      | some i =>
          simp only [elaborate, hi, Option.some.injEq] at decoded
          subst typed
          simp only [elaborate, hi, Core.Expr.map]
      | none =>
          cases hd : find? x a.discourse with
          | some d =>
              simp only [elaborate, hi, hd, Option.some.injEq] at decoded
              subst typed
              simp only [elaborate, hi, h.discourse x d hd, Core.Expr.map]
          | none =>
              cases hn : find? x a.nondiscourse with
              | none => simp [elaborate, hi, hd, hn] at decoded
              | some d =>
                  simp only [elaborate, hi, hd, hn, Option.map_some, Option.some.injEq] at decoded
                  subst typed
                  obtain ⟨hd', hn'⟩ := h.nondiscourse x d hd hn
                  simp only [elaborate, hi, hd', hn', Option.map_some, Core.Expr.map]
  | sequence x =>
      cases hi : index? x κ with
      | some i =>
          simp only [elaborate, hi, Option.some.injEq] at decoded
          subst typed
          simp only [elaborate, hi, Core.Expr.map]
      | none =>
          cases hd : find? x a.marker with
          | none => simp [elaborate, hi, hd] at decoded
          | some d =>
              simp only [elaborate, hi, hd, Option.map_some, Option.some.injEq] at decoded
              subst typed
              simp only [elaborate, hi, h.marker x d hd, Option.map_some, Core.Expr.map]
  | nil =>
      simp only [elaborate, Option.some.injEq] at decoded
      subst typed
      rfl
  | lift t ih =>
      cases ht : t.elaborate a ι κ <;> simp [elaborate, ht] at decoded
      subst typed
      simp [elaborate, ih _ ht, Core.Expr.map]
  | app t u it iu | cons t u it iu | append t u it iu =>
      cases ht : t.elaborate a ι κ <;> cases hu : u.elaborate a ι κ <;>
        simp [elaborate, ht, hu] at decoded
      subst typed
      simp [elaborate, it _ ht, iu _ hu, Core.Expr.map]

theorem Formula.elaborate_supports {S T : Core.Signature} {a : Names S} {b : Names T}
    {f : S ⟶ T} (h : a.Supports b f) (raw : Formula) :
    ∀ (ι κ : List String) (typed : Core.Formula S ι.length κ.length),
    raw.elaborate a ι κ = some typed → raw.elaborate b ι κ = some (typed.map f) := by
  induction raw with
  | equal t u | pred t u =>
      intro ι κ typed decoded
      cases ht : t.elaborate a ι κ <;> cases hu : u.elaborate a ι κ <;>
        simp [elaborate, ht, hu] at decoded
      subst typed
      simp [elaborate, t.elaborate_supports h ι κ _ ht, u.elaborate_supports h ι κ _ hu,
        Core.Formula.map]
  | tt | ff =>
      intro ι κ typed decoded
      simp only [elaborate, Option.some.injEq] at decoded
      subst typed
      rfl
  | neg p ih =>
      intro ι κ typed decoded
      cases hp : p.elaborate a ι κ <;> simp [elaborate, hp] at decoded
      subst typed
      simp [elaborate, ih ι κ _ hp, Core.Formula.map]
  | conj p q ip iq | disj p q ip iq | impl p q ip iq | iff p q ip iq =>
      intro ι κ typed decoded
      cases hp : p.elaborate a ι κ <;> cases hq : q.elaborate a ι κ <;>
        simp [elaborate, hp, hq] at decoded
      subst typed
      simp [elaborate, ip ι κ _ hp, iq ι κ _ hq, Core.Formula.map]
  | all x p ih | ex x p ih =>
      intro ι κ typed decoded
      cases hp : p.elaborate a (x::ι) κ <;> simp [elaborate, hp] at decoded
      subst typed
      simp [elaborate, ih (x::ι) κ _ hp, Core.Formula.map]
  | allSeq x p ih | exSeq x p ih =>
      intro ι κ typed decoded
      cases hp : p.elaborate a ι (x::κ) <;> simp [elaborate, hp] at decoded
      subst typed
      simp [elaborate, ih ι (x::κ) _ hp, Core.Formula.map]

end Silmaril.Logic.CommonLogic.Source
