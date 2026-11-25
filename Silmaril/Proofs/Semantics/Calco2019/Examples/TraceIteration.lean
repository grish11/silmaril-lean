module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Paths.Thms
public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceMonad.Thms
public import Silmaril.Semantics.Elgot.Thms

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.IterationProofs

open Silmaril.Elgot

variable {A X Y Z : Type u}

set_option backward.isDefEq.respectTransparency false

private theorem unfold_eq (f : X → TraceSet A (Y ⊕ X)) (g : X → TraceSet A Y) :
    traceStep f g = f >=> Sum.elim pure g :=
  funext (traceStep_eq_bind f g)

private theorem unfold_mapReturn (f : X → TraceSet A (Y ⊕ X))
    (k : Y → TraceSet A Z) (p : X → TraceSet A Z) :
    traceStep (mapReturn (m := TraceSet A) f k) p = f >=> Sum.elim k p := by
  rw [unfold_eq]
  funext x
  change ((f x >>= Sum.elim (fun y => k y >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)) >>=
    Sum.elim pure p) = _
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s <;> simp [Function.comp_def]

private theorem post_unfold (f : X → TraceSet A (Y ⊕ X)) (p : X → TraceSet A Y)
    (k : Y → TraceSet A Z) :
    (fun x => bindTraces (traceStep f p x) k) =
      traceStep (mapReturn (m := TraceSet A) f k) (fun x => bindTraces (p x) k) := by
  rw [unfold_eq, unfold_mapReturn]
  funext x
  change (f x >>= Sum.elim pure p) >>= k = f x >>= Sum.elim k (fun x => bindTraces (p x) k)
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s with
  | inl y => simp
  | inr x => rfl

private theorem natural_reverse (f : X → TraceSet A (Y ⊕ X)) (hf : TraceGuarded f)
    (k : Y → TraceSet A Z) :
    greatestTrace (mapReturn (m := TraceSet A) f k) ≤ (fun x => bindTraces (greatestTrace f x) k) := by
  classical
  let q := greatestTrace (mapReturn (m := TraceSet A) f k)
  let post (x : X) := bindTraces (greatestTrace f x) k
  let Bad (x : X) (t : Trace A Z) := t ∈ q x ∧ t ∉ post x
  have follow (x : X) (t : Trace A Z) (ht : Bad x t) :
      ∃ w x' tail, Sum.inl (w, Sum.inr x') ∈ f x ∧ Bad x' tail ∧ t = prepend w tail := by
    have hit := ht.1
    change t ∈ greatestTrace (mapReturn (m := TraceSet A) f k) x at hit
    rw [← greatestTrace_fix, unfold_mapReturn] at hit
    change t ∈ bindTraces (f x) (Sum.elim k q) at hit
    obtain ⟨s, hs, ho⟩ := hit
    cases s with
    | inr stream =>
      have orig := finite_sound (FiniteTraceRun.streams (Y := Y) hs)
      exact (ht.2 ⟨.inr stream, orig, ho⟩).elim
    | inl pair =>
      obtain ⟨word, y | x'⟩ := pair
      · have orig := finite_sound (FiniteTraceRun.returns hs)
        exact (ht.2 ⟨.inl (word, y), orig, ho⟩).elim
      · obtain ⟨tail, htail, he⟩ := ho
        refine ⟨word, x', tail, hs, ⟨htail, ?_⟩, he.symm⟩
        rintro ⟨s, hs', hproduces⟩
        have hpre : prepend word s ∈ greatestTrace f x := by
          rw [← greatestTrace_fix]
          exact Or.inr (Or.inr ⟨word, x', s, hs, hs', rfl⟩)
        apply ht.2
        refine ⟨prepend word s, hpre, ?_⟩
        rw [extend_prepend]
        exact ⟨tail, hproduces, he⟩
  have no_finite (x : X) (word : List A) (z : Z) : ¬ Bad x (.inl (word, z)) := by
    generalize hlen : word.length = n
    induction n using Nat.strong_induction_on generalizing x word with
    | ind n ih =>
      intro ht
      obtain ⟨w, x', tail, edge, bad, he⟩ := follow _ _ ht
      cases tail with
      | inr stream => cases he
      | inl pair =>
        obtain ⟨suffix, z'⟩ := pair
        change Sum.inl (word, z) = Sum.inl (w ++ suffix, z') at he
        cases he
        have hpos := List.length_pos_iff.mpr (hf _ _ _ edge)
        simp only [List.length_append] at hlen
        exact ih suffix.length (by omega) x' suffix rfl bad
  let r : X → TraceSet A Y := fun x => {t | ∃ s, t = .inr s ∧ Bad x (.inr s)}
  have hr : r ≤ traceStep f r := by
    intro x t ht
    obtain ⟨s, rfl, hbad⟩ := ht
    obtain ⟨w, x', tail, edge, bad, he⟩ := follow _ _ hbad
    cases tail with
    | inl pair => exact (no_finite x' pair.1 pair.2 bad).elim
    | inr tail =>
      exact Or.inr (Or.inr ⟨w, x', .inr tail, edge, ⟨tail, rfl, bad⟩,
        congrArg Sum.inr (Sum.inr.inj he)⟩)
  intro x t ht
  change t ∈ post x
  by_contra hbad
  cases t with
  | inl pair => exact no_finite x pair.1 pair.2 ⟨ht, hbad⟩
  | inr s =>
    have hit : Sum.inr s ∈ greatestTrace f x := le_greatestTrace f hr x ⟨s, rfl, ht, hbad⟩
    exact hbad ⟨.inr s, hit, rfl⟩

theorem natural (f : X → TraceSet A (Y ⊕ X)) (hf : TraceGuarded f)
    (k : Y → TraceSet A Z) :
    greatestTrace (mapReturn (m := TraceSet A) f k) = (fun x => bindTraces (greatestTrace f x) k) := by
  apply le_antisymm (natural_reverse f hf k)
  apply le_greatestTrace
  rw [← post_unfold, greatestTrace_fix]

private theorem unfold_flatten (f : X → TraceSet A ((Y ⊕ X) ⊕ X)) (p : X → TraceSet A Y) :
    traceStep (flattenBody (m := TraceSet A) f) p = f >=> Sum.elim (Sum.elim pure p) p := by
  rw [unfold_eq]
  funext x
  change ((f x >>= pure ∘ flatten) >>= Sum.elim pure p) = _
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s <;> simp [flatten]

private theorem unfold_twice (f : X → TraceSet A ((Y ⊕ X) ⊕ X))
    (h : X → TraceSet A (Y ⊕ X)) (p : X → TraceSet A Y) :
    traceStep (traceStep f h) p = f >=> Sum.elim (Sum.elim pure p) (traceStep h p) := by
  rw [unfold_eq f, unfold_eq (f >=> Sum.elim pure h)]
  funext x
  change ((f x >>= Sum.elim pure h) >>= Sum.elim pure p) = _
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s with
  | inl y => simp
  | inr x => exact (traceStep_eq_bind h p x).symm

theorem diagonal (f : X → TraceSet A ((Y ⊕ X) ⊕ X)) (hf : TraceGuarded f) :
    greatestTrace (flattenBody (m := TraceSet A) f) = greatestTrace (greatestTrace f) := by
  let h := greatestTrace f
  let p := greatestTrace h
  let q := greatestTrace (flattenBody (m := TraceSet A) f)
  have hh : traceStep f h = h := greatestTrace_fix f
  have hp : traceStep h p = p := greatestTrace_fix h
  have hq : traceStep (flattenBody (m := TraceSet A) f) q = q := greatestTrace_fix _
  apply le_antisymm
  · apply le_greatestTrace h
    rw [unfold_eq]
    change q ≤ fun x => bindTraces (h x) (Sum.elim pureTrace q)
    rw [← natural f hf]
    apply le_greatestTrace
    rw [unfold_mapReturn]
    change q ≤ f >=> Sum.elim (Sum.elim (pure : Y → TraceSet A Y) q) q
    rw [← unfold_flatten f q, hq]
  · apply le_greatestTrace (flattenBody (m := TraceSet A) f)
    have eq := unfold_twice f h p
    rw [hh, hp] at eq
    rw [unfold_flatten, ← eq]

theorem uniform (f : X → TraceSet A (Y ⊕ X)) (g : Z → TraceSet A (Y ⊕ Z))
    (h : Z → X) (comm : f ∘ h = g >=> liftPure (m := TraceSet A) (Sum.map id h)) :
    greatestTrace f ∘ h = greatestTrace g := by
  have image_eq (z : Z) : f (h z) = mapResult (Sum.map id h) '' g z :=
    (show f (h z) = bindTraces (g z) (pureTrace ∘ Sum.map id h) from congrFun comm z).trans
      (bind_pureMap (g z) (Sum.map id h))
  have image_mem (z : Z) {s : Trace A (Y ⊕ Z)} (hs : s ∈ g z) :
      mapResult (Sum.map id h) s ∈ f (h z) := image_eq z ▸ (show _ ∈ _ from ⟨s, hs, rfl⟩)
  have step (z : Z) (w : List A) (x' : X) (hit : Sum.inl (w, Sum.inr x') ∈ f (h z)) :
      ∃ z', h z' = x' ∧ Sum.inl (w, Sum.inr z') ∈ g z := by
    rw [image_eq] at hit
    obtain ⟨source, hs, he⟩ := hit
    cases source with
    | inr s => cases he
    | inl pair =>
      obtain ⟨w', y | z'⟩ := pair
      · cases he
      · simp [mapResult] at he
        obtain ⟨rfl, he⟩ := he
        exact ⟨z', he, hs⟩
  have returns (z : Z) (w : List A) (y : Y) (hit : Sum.inl (w, Sum.inl y) ∈ f (h z)) :
      Sum.inl (w, Sum.inl y) ∈ g z := by
    rw [image_eq] at hit
    obtain ⟨source, hs, he⟩ := hit
    cases source with
    | inr s => cases he
    | inl pair =>
      obtain ⟨w', y' | z'⟩ := pair
      · cases he
        exact hs
      · cases he
  have streams (z : Z) (s : ℕ → A) (hit : Sum.inr s ∈ f (h z)) : Sum.inr s ∈ g z := by
    rw [image_eq] at hit
    obtain ⟨source, hs, he⟩ := hit
    cases source with
    | inr s' => cases he; exact hs
    | inl pair => cases pair; cases he
  apply le_antisymm
  · apply le_greatestTrace
    intro z t ht
    change t ∈ greatestTrace f (h z) at ht
    rw [← greatestTrace_fix] at ht
    rcases ht with ⟨w, y, edge, rfl⟩ | ⟨s, edge, rfl⟩ | ⟨w, x', tail, edge, ht, rfl⟩
    · exact Or.inl ⟨w, y, returns z w y edge, rfl⟩
    · exact Or.inr (Or.inl ⟨s, streams z s edge, rfl⟩)
    · obtain ⟨z', rfl, edge'⟩ := step z w x' edge
      exact Or.inr (Or.inr ⟨w, z', tail, edge', ht, rfl⟩)
  · let r (x : X) : TraceSet A Y := {t | ∃ z, h z = x ∧ t ∈ greatestTrace g z}
    have hr : r ≤ traceStep f r := by
      intro x t ht
      obtain ⟨z, rfl, ht⟩ := ht
      rw [← greatestTrace_fix] at ht
      rcases ht with ⟨w, y, edge, rfl⟩ | ⟨s, edge, rfl⟩ | ⟨w, z', tail, edge, ht, rfl⟩
      · exact Or.inl ⟨w, y, image_mem z edge, rfl⟩
      · exact Or.inr (Or.inl ⟨s, image_mem z edge, rfl⟩)
      · exact Or.inr (Or.inr ⟨w, h z', tail, image_mem z edge, ⟨z', rfl, ht⟩, rfl⟩)
    intro z t ht
    exact le_greatestTrace f hr (h z) ⟨z, rfl, ht⟩

end Silmaril.Calco2019.Examples.Printing.IterationProofs
