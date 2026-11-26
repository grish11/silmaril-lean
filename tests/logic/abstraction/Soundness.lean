module

import Silmaril.Logic.Abstraction.Soundness.Thms

namespace Silmaril.Logic.Abstraction.SoundnessRegression

private abbrev everyShape : Shape where
  valence := 1
  arity := 1
  scope _ := {0}
  covers := by decide

private inductive Symbol : Shape → Type
  | every : Symbol everyShape

private def sig : Signature := ⟨Symbol⟩

private def every (p : Template sig 1) : Term sig 0 :=
  .app (.every : Symbol everyShape) (fun _ => p)

private def F {k : Nat} (t : Term sig k) : Term sig k :=
  .free (n := 1) 0 (fun _ => t)

private def G {k : Nat} (t : Term sig k) : Term sig k :=
  .free (n := 1) 7 (fun _ => t)

private def allF : Term sig 0 := every (F (.bound 0))

private def introRule : Rule sig := ⟨[⟨1, F (.bound 0)⟩], allF⟩
private def instRule : Rule sig := ⟨[⟨0, allF⟩], F (Term.var 0)⟩
private def theory : Set (Rule sig) := {introRule, instRule}

@[simp] private theorem antecedent_singleton (p : Premise sig) (t : Term sig 0) :
    (⟨[p], t⟩ : Rule sig).antecedent = {p} := by
  ext q
  simp [Rule.antecedent]

private def introSubst : Substitution sig
  | 1, 0 => some (F (G (.bound 0)))
  | _, _ => none

private def instSubst : Substitution sig
  | 0, 0 => some (G (Term.var 0))
  | _, _ => none

private def openedName : Fin 1 ↪ Nat where
  toFun _ := 0
  inj' := fun {i j} _ => Subsingleton.elim i j

private theorem introInstance :
    Derives theory {⟨1, F (G (.bound 0))⟩} (every (F (G (.bound 0)))) := by
  have h : introRule.Derivable theory := .axiom (by simp [theory])
  change Derives theory (⟨[⟨1, F (.bound 0)⟩], allF⟩ : Rule sig).antecedent allF at h
  rw [antecedent_singleton] at h
  have inst := h.subst introSubst
  rw [Set.image_singleton] at inst
  exact inst

private theorem instInstance : Derives theory {⟨0, allF⟩} (F (G (Term.var 0))) := by
  have h : instRule.Derivable theory := .axiom (by simp [theory])
  change Derives theory (⟨[⟨0, allF⟩], F (Term.var 0)⟩ : Rule sig).antecedent
    (F (Term.var 0)) at h
  rw [antecedent_singleton] at h
  have inst := h.subst instSubst
  rw [Set.image_singleton] at inst
  have premiseEq : Premise.subst instSubst ⟨0, allF⟩ = ⟨0, allF⟩ := rfl
  have conclusionEq : (F (Term.var 0) : Term sig 0).subst instSubst = F (G (Term.var 0)) := by
    simp only [F, G, Term.var, Term.subst, instSubst, Term.instantiate]
    congr 1
    funext i
    congr 1
    funext j
    congr 1
    exact Subsingleton.elim _ _
  rw [premiseEq, conclusionEq] at inst
  exact inst

private def consequence : Rule sig :=
  ⟨[⟨0, allF⟩], every (F (G (.bound 0)))⟩

-- Use instantiation at G[x] to discharge the unary template in universal introduction.
-- The eigenname x is also the schematic name of F at arity one, even in the supplying premise.
private theorem transfer : consequence.Derivable theory := by
  have consumer : Derives theory (insert ⟨1, F (G (.bound 0))⟩ ∅)
      (every (F (G (.bound 0)))) := by simpa using introInstance
  have h := Derives.infer openedName
    (p := F (G (.bound 0))) (Δ := {⟨0, allF⟩})
    (by intro i j k; trivial)
    (by
      intro p hp
      have eq : p = ⟨0, allF⟩ := hp
      subst p
      exact fun _ _ _ => trivial)
    consumer instInstance
  change Derives theory (⟨[⟨0, allF⟩], every (F (G (.bound 0)))⟩ : Rule sig).antecedent
    (every (F (G (.bound 0))))
  rw [antecedent_singleton]
  simpa using h

example : (institution.obj sig).Entails theory consequence := transfer.entails

-- The same name at arity zero would make the supplying premise ineligible.
example : ¬ (F (Term.var 0) : Term sig 0).Fresh (openedName 0) :=
  fun h => h 0 rfl

-- Add and remove a premise whose arity-zero name is absent from both sides of the rule.
example : consequence.Derivable theory := by
  apply Derives.varElim 0
  · intro p hp
    have eq : p = ⟨0, allF⟩ := by simpa [consequence, Rule.antecedent] using hp
    subst p
    exact fun _ _ => trivial
  · exact fun _ _ _ => trivial
  · exact Derives.add _ transfer

private def R {k : Nat} (a b : Term sig k) : Term sig k :=
  .free (n := 2) 8 (fun i => if i = 0 then a else b)

private def namesEmpty : Fin 0 ↪ Nat :=
  ⟨Fin.elim0, fun {i} => i.elim0⟩

private def names456 : Fin 3 ↪ Nat :=
  ⟨fun i => i.val + 4, fun {_ _} h => Fin.ext (Nat.add_right_cancel h)⟩

private def names64 : Fin 2 ↪ Nat :=
  ⟨fun i => 6 - 2 * i.val, fun {i j} h => by
    change 6 - 2 * i.val = 6 - 2 * j.val at h
    exact Fin.ext (by omega)⟩

private def body : Term sig 0 := R (Term.var 4) (Term.var 6)
private def old : Template sig 3 := R (.bound 0) (.bound 2)
private def reordered : Template sig 2 := R (.bound 1) (.bound 0)

-- Bind first adds three binders, capturing two occurrences. Then it swaps the two live
-- binders and removes the unused one, without moving or binding anything in the conclusion.
example : Derives (∅ : Set (Rule sig)) {⟨2, reordered⟩} body := by
  have start : Derives (∅ : Set (Rule sig)) (insert ⟨0, body⟩ ∅) body := by
    simpa using (Derives.assume body : Derives (∅ : Set (Rule sig)) {⟨0, body⟩} body)
  have added := Derives.bind (p := body) (q := old) namesEmpty names456
    (fun i => i.elim0) (by intro i j; by_cases h : j = 0 <;> simp [h, Term.Fresh])
    (by
      simp only [body, old, R, Term.openWith, Term.instantiate]
      congr 1
      funext i
      split <;> rfl)
    (fun i => i.elim0) start
  have changed := Derives.bind (p := old) (q := reordered) names456 names64
    (by intro i j; by_cases h : j = 0 <;> simp [h, Term.Fresh]) (by intro i j; by_cases h : j = 0 <;> simp [h, Term.Fresh])
    (by
      simp only [old, reordered, R, Term.openWith, Term.instantiate]
      congr 1
      funext i
      split <;> rfl)
    (by
      intro i absent
      have i0 : i ≠ 0 := fun h => absent ⟨1, by subst i; rfl⟩
      have i2 : i ≠ 2 := fun h => absent ⟨0, by subst i; rfl⟩
      have eq : i = 1 := by omega
      subst i
      intro j
      by_cases h : j = 0 <;> simp [Term.instantiate, Term.var, Term.Fresh, h, names456])
    added
  simpa using changed

private abbrev algebra (quantify : Operation Bool 1 → Bool) : Algebra sig where
  Carrier := Bool
  nonempty := ⟨false⟩
  op
    | .every, args => quantify (args 0)

private noncomputable abbrev model (quantify : Operation Bool 1 → Bool) : Model sig where
  algebra := algebra quantify
  truth := {
    Truth := Prop
    lattice := inferInstance
    includeValue := fun p => @decide p (Classical.propDecidable p)
    classify := fun b => b = true
    classify_include := fun p => @decide_eq_true_eq p (Classical.propDecidable p)
  }
  space := ValuationSpace.full (algebra quantify)

private def meet (f : Operation Bool 1) : Bool := f (fun _ => false) && f (fun _ => true)

private theorem satIntro : (model meet).Sat introRule := by
  intro ν _ b lower hb
  have atFalse := lower ⟨1, F (.bound 0)⟩ (by simp [introRule]) (fun _ => false) hb
  have atTrue := lower ⟨1, F (.bound 0)⟩ (by simp [introRule]) (fun _ => true) hb
  change ν 1 0 (fun _ => false) = true at atFalse
  change ν 1 0 (fun _ => true) = true at atTrue
  change meet (ν 1 0) = true
  simp [meet, atFalse, atTrue]

private theorem satInst : (model meet).Sat instRule := by
  intro ν _ b lower hb
  have all := lower ⟨0, allF⟩ (by simp [instRule]) Fin.elim0 hb
  change meet (ν 1 0) = true at all
  have both := Bool.and_eq_true_iff.mp all
  let value := (Term.var 0 : Term sig 0).eval (algebra meet) ν Fin.elim0
  change ν 1 0 (fun _ => value) = true
  cases value
  · exact both.1
  · exact both.2

example : (model meet).Sat consequence := by
  apply transfer.sound
  intro r hr
  rcases Set.mem_insert_iff.mp hr with rfl | hr
  · exact satIntro
  · have eq : r = instRule := hr
    exact eq ▸ satInst

-- Opposite constant interpretations of the abstraction invalidate the two theory axioms.
example : ¬ (model (fun _ => false)).Sat introRule := by
  intro sat
  let ν : Valuation Bool := fun _ _ _ => true
  have bad := sat ν (Set.mem_univ _) True (by
    intro p hp args
    obtain rfl := List.mem_singleton.mp hp
    intro _
    rfl) trivial
  change false = true at bad
  cases bad

example : ¬ (model (fun _ => true)).Sat instRule := by
  intro sat
  let ν : Valuation Bool := fun _ _ _ => false
  have bad := sat ν (Set.mem_univ _) True (by
    intro p hp args
    obtain rfl := List.mem_singleton.mp hp
    intro _
    rfl) trivial
  change false = true at bad
  cases bad

end Silmaril.Logic.Abstraction.SoundnessRegression
