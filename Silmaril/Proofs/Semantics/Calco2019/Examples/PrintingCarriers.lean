module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Carriers.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.Carriers.Proofs

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits

variable {A X S Z : Type u}

private theorem layer_map (f : S ⟶ Z) (t : X ⊕ (A × S)) :
    (layer A X).map f t = Sum.map id (Prod.map id f) t := by
  cases t <;> rfl

private def fold (a : X ⊕ (A × S) → S) (w : List A × X) : S :=
  w.1.foldr (fun c s => a (.inr (c, s))) (a (.inl w.2))

private def foldHom (B : Algebra (layer A X)) : algebra A X ⟶ B where
  f := TypeCat.ofHom (fold B.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro t
    cases t with
    | inl x => rfl
    | inr t => obtain ⟨a, w, x⟩ := t; rfl

noncomputable def initial (A X : Type u) : IsInitial (algebra A X) := by
  refine IsInitial.ofUniqueHom foldHom ?_
  intro B m
  apply Algebra.Hom.ext
  apply ConcreteCategory.hom_ext
  rintro ⟨w, x⟩
  induction w with
  | nil => exact (ConcreteCategory.congr_hom m.h (.inl x)).symm
  | cons a w ih =>
      have eq := (ConcreteCategory.congr_hom m.h (.inr (a, w, x))).symm
      change m.f (a :: w, x) = B.str (.inr (a, m.f (w, x))) at eq
      change m.f (a :: w, x) = B.str (.inr (a, (foldHom B).f (w, x)))
      rw [eq, ih]

section Unfold

variable (body : S → X ⊕ (A × S))

private inductive Returns : S → List A → X → Prop
  | ret {s x} : body s = .inl x → Returns s [] x
  | emit {s t a w x} : body s = .inr (a, t) → Returns t w x → Returns s (a :: w) x

private theorem returns_unique {s : S} {w v : List A} {x y : X}
    (h : Returns body s w x) (k : Returns body s v y) : (w, x) = (v, y) := by
  induction h generalizing v y with
  | ret eq =>
      cases k with
      | ret eq' => cases eq.symm.trans eq'; rfl
      | emit eq' _ => cases eq.symm.trans eq'
  | emit eq _ ih =>
      cases k with
      | ret eq' => cases eq.symm.trans eq'
      | emit eq' step =>
          cases eq.symm.trans eq'
          cases ih step
          rfl

private def ReturnsAt (s : S) : Prop := ∃ r : List A × X, Returns body s r.1 r.2

private theorem live_emits (s : {s // ¬ ReturnsAt body s}) : ∃ p, body s.1 = .inr p := by
  cases eq : body s.1 with
  | inl x => exact (s.2 ⟨([], x), .ret eq⟩).elim
  | inr p => exact ⟨p, rfl⟩

private noncomputable def liveStep (s : {s // ¬ ReturnsAt body s}) :
    A × {s // ¬ ReturnsAt body s} :=
  let p := (live_emits body s).choose
  (p.1, ⟨p.2, fun ⟨(w, x), h⟩ => s.2 ⟨(p.1 :: w, x), .emit (live_emits body s).choose_spec h⟩⟩)

private theorem liveStep_eq {s t : S} {a : A} (hs : ¬ ReturnsAt body s)
    (ht : ¬ ReturnsAt body t) (eq : body s = .inr (a, t)) :
    liveStep body ⟨s, hs⟩ = (a, ⟨t, ht⟩) := by
  have h := Sum.inr.inj ((live_emits body ⟨s, hs⟩).choose_spec.symm.trans eq)
  exact Prod.ext (congrArg (Prod.fst : A × S → A) h)
    (Subtype.ext (congrArg (Prod.snd : A × S → S) h))

private noncomputable def unfoldTrace (s : S) : Trace A X := by
  classical
  exact if h : ReturnsAt body s then .inl h.choose else .inr (Stream'.corec' (liveStep body) ⟨s, h⟩)

private theorem unfold_return {s : S} {w : List A} {x : X} (h : Returns body s w x) :
    unfoldTrace body s = .inl (w, x) := by
  classical
  let hr : ReturnsAt body s := ⟨(w, x), h⟩
  rw [unfoldTrace, dite_eq_left hr]
  exact congrArg Sum.inl (returns_unique body hr.choose_spec h)

private theorem unfold_observe (s : S) :
    observe (unfoldTrace body s) = Sum.map id (Prod.map id (unfoldTrace body)) (body s) := by
  classical
  cases eq : body s with
  | inl x => rw [unfold_return body (.ret eq)]; rfl
  | inr p =>
      obtain ⟨a, t⟩ := p
      by_cases ht : ReturnsAt body t
      · obtain ⟨⟨w, x⟩, h⟩ := ht
        change observe (unfoldTrace body s) = .inr (a, unfoldTrace body t)
        rw [unfold_return body (.emit eq h), unfold_return body h]
        rfl
      · have hs : ¬ ReturnsAt body s := by
          rintro ⟨⟨w, x⟩, h⟩
          cases h with
          | ret er => cases eq.symm.trans er
          | emit er h =>
              cases eq.symm.trans er
              exact ht ⟨(_, x), h⟩
        rw [unfoldTrace, dite_eq_right hs]
        change observe (Sum.inr (Stream'.corec' (liveStep body) ⟨s, hs⟩)) =
          .inr (a, unfoldTrace body t)
        rw [Stream'.corec'_eq, liveStep_eq body hs ht eq]
        simp [observe, unfoldTrace, ht]

end Unfold

private theorem observe_injective : Function.Injective (observe (A := A) (X := X)) := by
  let rebuild : X ⊕ (A × Trace A X) → Trace A X
    | .inl x => .inl ([], x)
    | .inr (a, t) => prepend [a] t
  have inverse : Function.LeftInverse rebuild observe := by
    intro t
    cases t with
    | inl p => obtain ⟨w, x⟩ := p; cases w <;> rfl
    | inr s => exact congrArg Sum.inr (Stream'.eta s)
  exact inverse.injective

private theorem finite_agreement (body : S → X ⊕ (A × S)) {k l : S → Trace A X}
    (hk : ∀ s, observe (k s) = Sum.map id (Prod.map id k) (body s))
    (hl : ∀ s, observe (l s) = Sum.map id (Prod.map id l) (body s))
    {s : S} {w : List A} {x : X} (finite : k s = .inl (w, x)) : l s = .inl (w, x) := by
  induction w generalizing s with
  | nil =>
      have step := hk s
      rw [finite] at step
      have ret : body s = .inl x := by cases h : body s <;> simp_all [observe]
      apply observe_injective
      rw [hl, ret]
      rfl
  | cons a w ih =>
      have step := hk s
      rw [finite] at step
      cases h : body s with
      | inl y => simp [h, observe] at step
      | inr p =>
          obtain ⟨b, t⟩ := p
          have e : b = a ∧ k t = .inl (w, x) := by simpa [h, observe] using step.symm
          obtain ⟨rfl, ek⟩ := e
          apply observe_injective
          rw [hl, h]
          change Sum.inr (b, l t) = Sum.inr (b, .inl (w, x))
          rw [ih ek]

private theorem unfold_unique (body : S → X ⊕ (A × S)) {k l : S → Trace A X}
    (hk : ∀ s, observe (k s) = Sum.map id (Prod.map id k) (body s))
    (hl : ∀ s, observe (l s) = Sum.map id (Prod.map id l) (body s)) : k = l := by
  funext s
  cases h : k s with
  | inl p => exact (finite_agreement body hk hl h).symm
  | inr p =>
      cases j : l s with
      | inl q => simpa only [h] using finite_agreement body hl hk j
      | inr q =>
          congr 1
          apply Stream'.eq_of_bisim
            (fun p q => ∃ t, k t = .inr p ∧ l t = .inr q) ?_ ⟨s, h, j⟩
          rintro p q ⟨t, hp, hq⟩
          have ep := hk t
          have eq := hl t
          rw [hp] at ep
          rw [hq] at eq
          cases ht : body t with
          | inl x => simp [observe, ht] at ep
          | inr r =>
              obtain ⟨a, t'⟩ := r
              simp [observe, ht] at ep eq
              exact ⟨ep.1.trans eq.1.symm, t', ep.2.symm, eq.2.symm⟩

private noncomputable def unfoldHom (B : Coalgebra (layer A X)) : B ⟶ coalgebra A X where
  f := TypeCat.ofHom (unfoldTrace B.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (layer_map _ (B.str s)).trans (unfold_observe B.str s).symm

noncomputable def terminal (A X : Type u) : IsTerminal (coalgebra A X) := by
  refine IsTerminal.ofUniqueHom unfoldHom ?_
  intro B m
  apply Coalgebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro s
  apply congrFun (unfold_unique B.str ?_ (unfold_observe B.str)) s
  intro t
  exact (ConcreteCategory.congr_hom m.h t).symm.trans (layer_map m.f (B.str t))

end Silmaril.Calco2019.Examples.Printing.Carriers.Proofs
