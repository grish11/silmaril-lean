module

public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceIteration.Defs
public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Thms
import Silmaril.Proofs.Semantics.Calco2019.Examples.TraceIteration

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.ProductiveProofs

open Silmaril.Elgot

variable {A X Y Z : Type u}

set_option backward.isDefEq.respectTransparency false

private theorem bind_silent (p : TraceSet A X) (k : X → TraceSet A Y) (y : Y)
    (hit : Sum.inl ([], y) ∈ bindTraces p k) :
    ∃ x, Sum.inl ([], x) ∈ p ∧ Sum.inl ([], y) ∈ k x := by
  obtain ⟨s, hs, ht⟩ := hit
  cases s with
  | inr stream =>
    change Sum.inl ([], y) = Sum.inr stream at ht
    cases ht
  | inl pair =>
    obtain ⟨word, x⟩ := pair
    obtain ⟨tail, htail, he⟩ := ht
    cases tail with
    | inr stream => cases he
    | inl pair =>
      obtain ⟨suffix, y'⟩ := pair
      change Sum.inl (word ++ suffix, y') = Sum.inl ([], y) at he
      have ⟨hw, hy⟩ := Prod.mk.inj (Sum.inl.inj he)
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw
      exact ⟨x, hs, hy ▸ htail⟩

@[expose] def guard (A : Type u) : TypeKleisli.Guard (NonemptyTrace A) where
  holds := ProductiveGuard
  trivial {X Y Z} f x z word hit hw := by
    subst word
    change Sum.inl ([], .inr z) ∈ bindTraces (f x).1 (pureTrace ∘ (Sum.inl : Y → Y ⊕ Z)) at hit
    obtain ⟨y, _, hy⟩ := bind_silent _ _ _ hit
    change Sum.inl ([], Sum.inr z) = Sum.inl ([], Sum.inl y) at hy
    cases hy
  parallel hf hg := by
    intro u
    cases u with
    | inl x => exact hf x
    | inr y => exact hg y
  compose {X Y Z V W} {f g} h hf hg x z word hit hw := by
    subst word
    change Sum.inl ([], .inr z) ∈
      bindTraces (f x).1 (fun s => (Sum.elim g h s).1) at hit
    obtain ⟨y | w, hsrc, hdst⟩ := bind_silent _ _ _ hit
    · exact hg y z [] hdst rfl
    · exact hf x w [] hsrc rfl

private theorem proj_mapReturn (f : X → NonemptyTrace A (Y ⊕ X)) (g : Y → NonemptyTrace A Z) :
    (fun x => (mapReturn f g x).1) =
      mapReturn (m := TraceSet A) (fun x => (f x).1) (fun y => (g y).1) := by
  funext x
  unfold mapReturn
  rw [val_traceBind]
  change bindTraces (f x).1 _ = bindTraces (f x).1 _
  congr 1
  funext s
  cases s <;> rfl

noncomputable def laws (A : Type u) : TypeKleisli.Iteration (NonemptyTrace A) (guard A) where
  run f hf := productiveIter f hf
  fixpoint f hf := by
    funext x
    apply Subtype.ext
    have h := congrFun (greatestTrace_fix (fun x => (f x).1)) x
    rw [traceStep_eq_bind] at h
    change bindTraces (f x).1 (fun s => (Sum.elim pure (productiveIter f hf) s).1) = _
    refine (congrArg (bindTraces (f x).1) ?_).trans h
    funext s
    cases s <;> rfl
  naturality f g hf hg := by
    funext x
    apply Subtype.ext
    change greatestTrace (fun a => (mapReturn f g a).1) x =
      bindTraces (greatestTrace (fun a => (f a).1) x) (fun y => (g y).1)
    rw [proj_mapReturn]
    exact congrFun (IterationProofs.natural (fun a => (f a).1) hf (fun y => (g y).1)) x
  codiagonal f _ hi ho hm := by
    funext x
    apply Subtype.ext
    change greatestTrace (flattenBody (m := TraceSet A) (fun a => (f a).1)) x =
      greatestTrace (greatestTrace (fun a => (f a).1)) x
    exact congrFun (IterationProofs.diagonal (fun a => (f a).1) hi) x
  uniformity f g h hf hg comm := by
    have hc : (fun x => (f (h x)).1) =
        (fun x => (g x).1) >=> liftPure (m := TraceSet A) (Sum.map id h) := by
      funext z
      exact congrArg Subtype.val (congrFun comm z)
    funext z
    apply Subtype.ext
    exact congrFun (IterationProofs.uniform (fun x => (f x).1) (fun z => (g z).1) h hc) z

theorem laws_run (f : X → NonemptyTrace A (Y ⊕ X)) (hf : (guard A).holds f) :
    (laws A).run f hf = productiveIter f hf := by
  unfold laws
  rfl

theorem canonical_not_least (a : A) : ¬ greatestTrace (traceLoop a) ≤ finiteSolution a := by
  intro h
  have hinf : Sum.inr (fun _ => a) ∈ productiveSolution a () := Or.inl rfl
  have hle : productiveSolution a ≤ greatestTrace (traceLoop a) :=
    le_greatestTrace _ (productive_fixpoint a).ge
  obtain ⟨_, hfalse⟩ := h () (hle () hinf)
  cases hfalse

theorem productive_not_unique (a : Type) (letter : a) : ¬ (guard a).HasUniqueFixpoints := by
  let f (x : Unit) : NonemptyTrace a (Unit ⊕ Unit) :=
    ⟨traceLoop letter x, ⟨.inl ([], .inl ()), Or.inl rfl⟩⟩
  let p (x : Unit) : NonemptyTrace a Unit := ⟨finiteSolution letter x, (solutions_nonempty letter x).1⟩
  let q (x : Unit) : NonemptyTrace a Unit := ⟨productiveSolution letter x, (solutions_nonempty letter x).2⟩
  have fix (g : Unit → NonemptyTrace a Unit)
      (hg : traceStep (traceLoop letter) (fun x => (g x).1) = fun x => (g x).1) :
      f >=> Sum.elim pure g = g := by
    funext x
    apply Subtype.ext
    have h := congrFun hg x
    rw [traceStep_eq_bind] at h
    change bindTraces (traceLoop letter x) (fun s => (Sum.elim pure g s).1) = (g x).1
    convert h using 2
    funext s
    cases s <;> rfl
  intro unique
  obtain ⟨r, _, hu⟩ := unique f (traceLoop_guarded letter)
  have he := (hu p (fix p (finite_fixpoint letter))).trans (hu q (fix q (productive_fixpoint letter))).symm
  exact solutions_distinct letter (funext fun x => congrArg Subtype.val (congrFun he x))

end Silmaril.Calco2019.Examples.Printing.ProductiveProofs
