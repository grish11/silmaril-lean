module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Reflection
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Unrolling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonRounds

/-! # Every round count unrolls in ordered-trace Kleisli models

This is a calculation in models. It derives no equation of the quotient.
-/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithCaseBind.BitQuery (signature Trace)
open Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofRegion ofType sumCofan sumCofanIsColimit)
open Paper.Extension.Singleton.Rounds
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open CategoryTheory CategoryTheory.Limits

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
local notation "T" => Coordinates.ofModel (τ := Ty Empty) J M
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false

set_option backward.isDefEq.respectTransparency false

section Monad

variable {A B : Type}

/-- Up to `n + 1` rounds of a step of the trace monad. -/
def roundsM (f : A → Trace (B ⊕ A)) : Nat → A → Trace (B ⊕ A)
  | 0 => f
  | n + 1 => fun a => f a >>= Sum.elim (fun b => pure (Sum.inl b)) (roundsM f n)

/-- What one outcome of a block contributes to the one-round loop. -/
def Advances (f : A → Trace (B ⊕ A)) (a : A) (y : Except Bool (B ⊕ A)) (w : Word) : Prop :=
  match y with
  | .error t => (Except.error t, w) ∈ (Silmaril.Elgot.iter f a).outcomes
  | .ok (.inl b) => (Except.ok b, w) ∈ (Silmaril.Elgot.iter f a).outcomes
  | .ok (.inr next) => ∀ r v, (r, v) ∈ (Silmaril.Elgot.iter f next).outcomes →
      (r, w * v) ∈ (Silmaril.Elgot.iter f a).outcomes

theorem roundsM_advances (f : A → Trace (B ⊕ A)) :
    ∀ (n : Nat) (a : A) (y : Except Bool (B ⊕ A)) (w : Word),
      (y, w) ∈ (roundsM f n a).outcomes → Advances f a y w
  | 0, a, y, w, h => by
    rcases y with t | b | next
    · exact (iter_unfold f a).2 (.inl ⟨t, rfl, h⟩)
    · exact (iter_unfold f a).2 (.inr (.inl ⟨b, rfl, h⟩))
    · intro r v hv
      exact (iter_unfold f a).2 (.inr (.inr ⟨next, w, v, h, hv, rfl⟩))
  | n + 1, a, y, w, h => by
    have h' : (y, w) ∈ (f a >>= Sum.elim (fun b => pure (Sum.inl b)) (roundsM f n)).outcomes := h
    rcases Tagged.mem_bind.1 h' with ⟨t, rfl, ht⟩ | ⟨x, u, v, hx, hk, rfl⟩
    · exact (iter_unfold f a).2 (.inl ⟨t, rfl, ht⟩)
    · rcases x with b | a1
      · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
        exact (iter_unfold f a).2 (.inr (.inl ⟨b, rfl, (mul_one u).symm ▸ hx⟩))
      · have ih := roundsM_advances f n a1 y v hk
        rcases y with t | b | next
        · exact (iter_unfold f a).2 (.inr (.inr ⟨a1, u, v, hx, ih, rfl⟩))
        · exact (iter_unfold f a).2 (.inr (.inr ⟨a1, u, v, hx, ih, rfl⟩))
        · intro r v' hv'
          exact (iter_unfold f a).2
            (.inr (.inr ⟨a1, u, v * v', hx, ih r v' hv', (mul_assoc u v v').symm⟩))

theorem roundsM_error (f : A → Trace (B ⊕ A)) (j : Nat) {a : A} {t : Bool} {w : Word}
    (h : (Except.error t, w) ∈ (f a).outcomes) : (Except.error t, w) ∈ (roundsM f j a).outcomes := by
  cases j with
  | zero => exact h
  | succ j => exact Tagged.mem_bind.2 (.inl ⟨t, rfl, h⟩)

theorem roundsM_ret (f : A → Trace (B ⊕ A)) (j : Nat) {a : A} {b : B} {w : Word}
    (h : (Except.ok (Sum.inl b), w) ∈ (f a).outcomes) :
    (Except.ok (Sum.inl b), w) ∈ (roundsM f j a).outcomes := by
  cases j with
  | zero => exact h
  | succ j => exact Tagged.mem_bind.2 (.inr ⟨.inl b, w, 1, h, mem_pure.2 ⟨rfl, rfl⟩, mul_one w⟩)

/-- In the trace monad the loop on any number of rounds has the
observations of the loop on one round, complete or not. -/
theorem iter_roundsM (f : A → Trace (B ⊕ A)) (n : Nat) (a : A) :
    (Silmaril.Elgot.iter (roundsM f n) a).outcomes = (Silmaril.Elgot.iter f a).outcomes := by
  apply Set.Subset.antisymm
  · refine iter_induction (roundsM f n) (fun a => (Silmaril.Elgot.iter f a).outcomes) ?_ ?_ ?_ a
    · intro a t w h
      exact roundsM_advances f n a _ w h
    · intro a b w h
      exact roundsM_advances f n a _ w h
    · intro a next u r v hu hv
      exact roundsM_advances f n a _ u hu r v hv
  · have fix : ∀ a, Silmaril.Elgot.iter (roundsM f n) a =
        roundsM f n a >>= Sum.elim pure (Silmaril.Elgot.iter (roundsM f n)) :=
      congrFun (Silmaril.Elgot.ExceptT.fixpoint (roundsM f n))
    intro obs h
    have all := iter_induction f
      (fun a => {obs | ∀ j, obs ∈
        (roundsM f j a >>= Sum.elim pure (Silmaril.Elgot.iter (roundsM f n))).outcomes})
      ?_ ?_ ?_ a h
    · rw [fix]
      exact all n
    · intro a t w h j
      exact Tagged.mem_bind.2 (.inl ⟨t, rfl, roundsM_error f j h⟩)
    · intro a b w h j
      exact Tagged.mem_bind.2 (.inr ⟨.inl b, w, 1, roundsM_ret f j h, mem_pure.2 ⟨rfl, rfl⟩, mul_one w⟩)
    · intro a next u r v hu hv j
      cases j with
      | zero =>
        refine Tagged.mem_bind.2 (.inr ⟨.inr next, u, v, hu, ?_, rfl⟩)
        change (r, v) ∈ (Silmaril.Elgot.iter (roundsM f n) next).outcomes
        rw [fix]
        exact hv n
      | succ j =>
        change (r, u * v) ∈ ((f a >>= Sum.elim (fun b => pure (Sum.inl b)) (roundsM f j)) >>=
          Sum.elim pure (Silmaril.Elgot.iter (roundsM f n))).outcomes
        rw [bind_assoc]
        exact Tagged.mem_bind.2 (.inr ⟨.inr next, u, v, hu, hv j, rfl⟩)

end Monad

theorem sumIso_inv (B A : Ty Empty) : ((T).sumIso B A).inv =
    (Kleisli.Type.coprodIsoSum Trace ((J).obj ((M).obj B)) ((J).obj ((M).obj A))).hom :=
  (Category.comp_id _).symm.trans ((Iso.inv_comp_eq _).2 (sumIso_coprodIsoSum B A).symm)

section Coherent

-- The instruction interpretation is the parameter of this section.
set_option linter.concreteInstances false

variable [inst : InstructionModel J M signature.Instr] [RegionTypingCoherent (Φ := signature.Instr) J M]
  {A B D : Ty Empty}

theorem map_inl : (F).map (sumCofan N B A).inl =
    coprod.inl ≫ (Kleisli.Type.coprodIsoSum Trace ((J).obj ((M).obj B)) ((J).obj ((M).obj A))).hom := by
  have p := (Paper.Extension.Singleton.denoteFunctor_preserves J M (fun _ _ => ⟨rfl, rfl⟩)
    (WithGuardedTablePacking.seedDenotes (Φ := signature.Instr) false J M (fun _ _ => ⟨rfl, rfl⟩))).inl B A
  simp only [mapInCoordinates, Iso.refl_inv, Iso.refl_hom, Category.id_comp] at p
  exact ((Category.comp_id _).symm.trans p).trans (congrArg (coprod.inl ≫ ·) (sumIso_inv B A))

theorem map_inr : (F).map (sumCofan N B A).inr =
    coprod.inr ≫ (Kleisli.Type.coprodIsoSum Trace ((J).obj ((M).obj B)) ((J).obj ((M).obj A))).hom := by
  have p := (Paper.Extension.Singleton.denoteFunctor_preserves J M (fun _ _ => ⟨rfl, rfl⟩)
    (WithGuardedTablePacking.seedDenotes (Φ := signature.Instr) false J M (fun _ _ => ⟨rfl, rfl⟩))).inr B A
  simp only [mapInCoordinates, Iso.refl_inv, Iso.refl_hom, Category.id_comp] at p
  exact ((Category.comp_id _).symm.trans p).trans (congrArg (coprod.inr ≫ ·) (sumIso_inv B A))

theorem inl_of (b : value B) :
    ((F).map ((sumCofan N B A).inl : ofType N B ⟶ ofType N (Silmaril.coprod B A))).of b =
      (pure (Sum.inl b) : Trace (value B ⊕ value A)) :=
  (congrArg (fun g : (J).obj ((M).obj B) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) => g.of b)
    ((map_inl (inst := inst) (A := A) (B := B)).trans
      (Kleisli.Type.inl_coprodIsoSum_hom Trace _ _))).trans rfl

theorem inr_of (a : value A) :
    ((F).map ((sumCofan N B A).inr : ofType N A ⟶ ofType N (Silmaril.coprod B A))).of a =
      (pure (Sum.inr a) : Trace (value B ⊕ value A)) :=
  (congrArg (fun g : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) => g.of a)
    ((map_inr (inst := inst) (A := A) (B := B)).trans
      (Kleisli.Type.inr_coprodIsoSum_hom Trace _ _))).trans rfl

theorem copair_inl_of (f : ofType N B ⟶ ofType N D) (g : ofType N A ⟶ ofType N D) (b : value B) :
    ((F).map (exactCopair N f g)).of (Sum.inl b : value B ⊕ value A) = ((F).map f).of b := by
  let k : (J).obj ((M).obj (Silmaril.coprod B A)) ⟶ (J).obj ((M).obj D) := (F).map (exactCopair N f g)
  let i : (J).obj ((M).obj B) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) := (F).map (sumCofan N B A).inl
  have fac : (sumCofan N B A).inl ≫ exactCopair N f g = f :=
    (sumCofanIsColimit N B A).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩
  have comp : i ≫ k = (F).map f := ((F).map_comp _ _).symm.trans (congrArg (F).map fac)
  have run := congrFun (Kleisli.Type.comp_of_eq_kleisliRight Trace i k) b
  have left := congrArg (fun g : (J).obj ((M).obj B) ⟶ (J).obj ((M).obj D) => g.of b) comp
  refine Eq.symm (left.symm.trans (run.trans ?_))
  change Bind.bind (m := Trace) (i.of b) (fun y => k.of y) = k.of (Sum.inl b)
  rw [show i.of b = (pure (Sum.inl b) : Trace (value B ⊕ value A)) from inl_of b, pure_bind]

theorem copair_inr_of (f : ofType N B ⟶ ofType N D) (g : ofType N A ⟶ ofType N D) (a : value A) :
    ((F).map (exactCopair N f g)).of (Sum.inr a : value B ⊕ value A) = ((F).map g).of a := by
  let k : (J).obj ((M).obj (Silmaril.coprod B A)) ⟶ (J).obj ((M).obj D) := (F).map (exactCopair N f g)
  let i : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) := (F).map (sumCofan N B A).inr
  have fac : (sumCofan N B A).inr ≫ exactCopair N f g = g :=
    (sumCofanIsColimit N B A).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩
  have comp : i ≫ k = (F).map g := ((F).map_comp _ _).symm.trans (congrArg (F).map fac)
  have run := congrFun (Kleisli.Type.comp_of_eq_kleisliRight Trace i k) a
  have left := congrArg (fun g : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj D) => g.of a) comp
  refine Eq.symm (left.symm.trans (run.trans ?_))
  change Bind.bind (m := Trace) (i.of a) (fun y => k.of y) = k.of (Sum.inr a)
  rw [show i.of a = (pure (Sum.inr a) : Trace (value B ⊕ value A)) from inr_of a, pure_bind]

theorem then_run (s t : ofType N A ⟶ ofType N (Silmaril.coprod B A)) (a : value A) :
    (((F).map (thenExact N s t)).of a : Trace (value B ⊕ value A)) =
      Bind.bind (m := Trace) (((F).map s).of a : Trace (value B ⊕ value A))
        (Sum.elim (fun b => (pure (Sum.inl b) : Trace (value B ⊕ value A)))
          (fun x => (((F).map t).of x : Trace (value B ⊕ value A)))) := by
  let u : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) := (F).map s
  let c : (J).obj ((M).obj (Silmaril.coprod B A)) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) :=
    (F).map (exactCopair N (sumCofan N B A).inl t)
  have comp : (F).map (thenExact N s t) = u ≫ c := (F).map_comp _ _
  have run := congrFun (Kleisli.Type.comp_of_eq_kleisliRight Trace u c) a
  have left := congrArg
    (fun g : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) => g.of a) comp
  refine (left.trans run).trans ?_
  change Bind.bind (m := Trace) (u.of a) (fun y => c.of y) = _
  congr 1
  funext v
  rcases v with b | x
  · exact (copair_inl_of _ t b).trans (inl_of b)
  · exact copair_inr_of _ t x

theorem rounds_run (s : ofType N A ⟶ ofType N (Silmaril.coprod B A)) :
    ∀ n, (fun x : value A => (((F).map (rounds N s n)).of x : Trace (value B ⊕ value A))) =
      roundsM (fun x => ((F).map s).of x) n
  | 0 => rfl
  | n + 1 => funext fun a => (then_run s (rounds N s n) a).trans
      (congrArg (fun k => Bind.bind (m := Trace) (((F).map s).of a : Trace (value B ⊕ value A))
        (Sum.elim (fun b => (pure (Sum.inl b) : Trace (value B ⊕ value A))) k)) (rounds_run s n))

theorem iterate_run {r : Region signature.Instr} (hr : ValueBranches [A] r [Silmaril.coprod B A])
    (a : value A) :
    (denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hr).hasType).of a =
      Silmaril.Elgot.iter (m := Trace)
        (fun x : value A => (((F).map (ofRegion N hr)).of x : Trace (value B ⊕ value A))) a := by
  have literal : (F).map (ofRegion N (SyntacticCategory.iterateRegion_valueBranches hr)) =
      denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hr).hasType :=
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩)
      (WithGuardedTablePacking.seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩)) _
  have iterated : (F).map (Paper.Extension.Singleton.iterateSum N (ofRegion N hr)) =
      denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hr).hasType :=
    (congrArg (F).map (SingletonRounds.ofRegion_iterateRegion N hr)).symm.trans literal
  exact (congrArg (fun g : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj B) => g.of a) iterated).symm.trans
    (map_iterateSum_of (ofRegion N hr) a)

/-- In every coherent trace model, the written loop on any number of
rounds of a guarded step has the arrow of the written loop on one round. -/
theorem rounds_model {s : Region signature.Instr} (hs : ValueBranches [A] s [Silmaril.coprod B A])
    (n : Nat) (a : value A) :
    (denoteSingletonRegion J M
      (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType).of a =
    (denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hs).hasType).of a := by
  apply Tagged.outcomes_injective
  rw [iterate_run (roundsRegion_typed hs n) a, iterate_run hs a, ofRegion_roundsRegion, rounds_run]
  exact iter_roundsM _ n a

end Coherent

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop
