module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RelayTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.MixedSeparation

/-! # The relay table in the four-reply interpreter -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open Paper.Extension.Singleton (ofRegion ofType sumCofan)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "Lit" => ofRegion N

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

theorem injOf_run {X : Ty Empty} {a : Tm signature.Instr} (ha : Tm.BranchValue [X] a State)
    (v : value X → value State)
    (base : ∀ x, (((F).map (Lit (brOf ha))).of x : Trace (value State)) = (pure (v x) : Trace (value State))) :
    ∀ (K : Nat) (j : Fin (K + 1)) (x : value X),
      (((F).map (Lit (brOf (injTm_typed ha K j)))).of x : Trace (value (States K))) =
        (pure (injVal K j (v x)) : Trace (value (States K)))
  | 0, _, x => base x
  | K + 1, j, x => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (inl_run (B := States K) ha x).trans
        ((congrArg (Bind.bind (m := Trace) · _) (base x)).trans (pure_bind _ _))
    · exact (inr_run (A := State) (injTm_typed ha K j) x).trans
        ((congrArg (Bind.bind (m := Trace) · _) (injOf_run ha v base K j x)).trans (pure_bind _ _))

theorem bitState_run (b : value Bit) :
    (((F).map (Lit (brOf (A := State) (.inl (.var (i := 0) rfl))))).of b : Trace (value State)) =
      (pure (Sum.inl b) : Trace (value State)) :=
  (inl_run (B := packedExitType ([] : LCtx (Ty Empty))) (.var (i := 0) rfl) b).trans
    ((congrArg (Bind.bind (m := Trace) · _) (id_run Bit b)).trans (pure_bind _ _))

theorem relayRoute_run (K : Nat) (j₁ j₂ : Fin (K + 1)) (v : value Bit ⊕ value State) :
    (((F).map (Lit (relayRoute_typed K j₁ j₂))).of v : Trace (value Bit ⊕ value (States K))) =
      relayRouteVal K j₁ j₂ v := by
  have arrow : Lit (relayRoute_typed K j₁ j₂) = exactCopair N (Lit (stay_typed K j₁)) (Lit (goto_typed K j₂)) :=
    (exactCopair_ofRegion N (stay_typed K j₁) (goto_typed K j₂)).symm
  rw [arrow]
  rcases v with b | y
  · exact (copair_inl_of _ _ b).trans
      ((inr_run (A := Bit) (injTm_typed (.inl (.var (i := 0) rfl)) K j₁) b).trans
        ((congrArg (Bind.bind (m := Trace) · _)
          (injOf_run (.inl (.var (i := 0) rfl)) (fun b => Sum.inl b) bitState_run K j₁ b)).trans
            (pure_bind _ _)))
  · exact (copair_inr_of _ _ y).trans
      ((inr_run (A := Bit) (injTm_typed (.var (i := 0) rfl) K j₂) y).trans
        ((congrArg (Bind.bind (m := Trace) · _) (inj_run K j₂ y)).trans (pure_bind _ _)))

theorem row_run (K : Nat) (p : Program) (j : Fin (K + 1)) (s : value State) :
    (((F).map (Lit (row_typed K p j))).of s : Trace (value Bit ⊕ value (States K))) =
      Bind.bind (m := Trace) (stepModel p s) (routeVal K j) := by
  have arrow : Lit (row_typed K p j) = stepArrow p ≫ Lit (route_typed K j) :=
    (congrArg (Paper.Extension.Singleton.projection N).map (Tables.row_arrow K p j)).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  rw [arrow]
  exact (comp_run _ _ s).trans
    (congr (congrArg (Bind.bind (m := Trace)) (BitLoop.step_run p s)) (funext (route_run K j)))

theorem relayRow_run (K : Nat) (p : Program) (j₁ j₂ : Fin (K + 1)) (s : value State) :
    (((F).map (Lit (relayRow_typed K p j₁ j₂))).of s : Trace (value Bit ⊕ value (States K))) =
      Bind.bind (m := Trace) (stepModel p s) (relayRouteVal K j₁ j₂) := by
  have arrow : Lit (relayRow_typed K p j₁ j₂) = stepArrow p ≫ Lit (relayRoute_typed K j₁ j₂) :=
    (congrArg (Paper.Extension.Singleton.projection N).map (Tables.relayRow_arrow K p j₁ j₂)).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  rw [arrow]
  exact (comp_run _ _ s).trans
    (congr (congrArg (Bind.bind (m := Trace)) (BitLoop.step_run p s)) (funext (relayRoute_run K j₁ j₂)))

variable (K : Nat) (q p : Program) (j : Fin (K + 1))

theorem relay_step_inj (i : Fin (K + 2)) (s : value State) :
    relayStepM K q p j (injVal (K + 1) i s) = ((F).map (Lit (relayRows_typed K q p j i))).of s := by
  have rows := dispatch_run (K + 1) (relayRows_typed K q p j) i s
  have literal := congrArg (fun h : (J).obj ((M).obj (States (K + 1))) ⟶ (J).obj ((M).obj _) =>
    h.of (injVal (K + 1) i s)) (lit_run (dispatch_typed (K + 1) (relayRows_typed K q p j)))
  exact literal.symm.trans rows

/-- The untouched state: the step of `q`, then back to itself or into the block. -/
theorem relay_step_zero (s : value State) :
    relayStepM K q p j (injVal (K + 1) 0 s) =
      Bind.bind (m := Trace) (stepModel q s) (relayRouteVal (K + 1) 0 j.succ) :=
  (relay_step_inj K q p j 0 s).trans (relayRow_run (K + 1) q 0 j.succ s)

/-- A block state: the step of `p`, then outward or back to the untouched state. -/
theorem relay_step_succ (i : Fin (K + 1)) (s : value State) :
    relayStepM K q p j (injVal (K + 1) i.succ s) =
      Bind.bind (m := Trace) (stepModel p s) (routeVal (K + 1) 0) :=
  (relay_step_inj K q p j i.succ s).trans (row_run (K + 1) p 0 s)

theorem relay_obs_eq (i : Fin (K + 2)) (g : Bool) :
    relayObservations K q p j i g =
      (Silmaril.Elgot.iter (m := Trace) (relayStepM K q p j) (injVal (K + 1) i (Sum.inl (bit g)))).outcomes := by
  have arrow : Lit (relayFan_typed K q p j i) =
      Lit (entry_typed (K + 1) i) ≫ Lit (dispatchLoop_typed (relayRows_typed K q p j)) :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (entry_typed (K + 1) i)
        (dispatchLoop_typed (relayRows_typed K q p j)) (relayFan_typed K q p j i)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  have run := comp_run (Lit (entry_typed (K + 1) i)) (Lit (dispatchLoop_typed (relayRows_typed K q p j)))
    (Sum.inl (bit g))
  rw [← arrow, inj_run, pure_bind] at run
  have lhs := congrArg (fun h : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) =>
    h.of (Sum.inl (bit g))) (lit_run (relayFan_typed K q p j i))
  have rhs := congrArg (fun h : (J).obj ((M).obj (States (K + 1))) ⟶ (J).obj ((M).obj Bit) =>
    h.of (injVal (K + 1) i (Sum.inl (bit g)))) (lit_run (dispatchLoop_typed (relayRows_typed K q p j)))
  have loop : (denoteSingletonRegion J M (dispatchLoop_typed (relayRows_typed K q p j)).hasType).of
      (injVal (K + 1) i (Sum.inl (bit g))) =
      Silmaril.Elgot.iter (m := Trace) (relayStepM K q p j) (injVal (K + 1) i (Sum.inl (bit g))) := by
    refine (iterate_run (dispatch_typed (K + 1) (relayRows_typed K q p j)) _).trans ?_
    rw [lit_run (dispatch_typed (K + 1) (relayRows_typed K q p j))]
    rfl
  exact congrArg Tagged.outcomes (lhs.symm.trans (run.trans (rhs.trans loop)))

/-- A poll step followed by a pure routing contributes one event with the
poll's label and no fault. -/
theorem poll_bind_outcome {Z : Type} (a : Poll) (g : Bool) (k : value Bit ⊕ value State → Trace Z)
    (hk : ∀ v, ∃ z, k v = pure z) {y : Except Bool Z} {w : Word}
    (hm : (y, w) ∈ (Bind.bind (m := Trace) (stepModel a.program (Sum.inl (bit g))) k).outcomes) :
    ∃ tag pl, w = FreeMonoid.of (event a.label g (tag, pl)) ∧ ∃ z, y = .ok z := by
  rw [Tagged.mem_bind] at hm
  rcases hm with ⟨t', rfl, ht⟩ | ⟨x, u, v, hx, hkv, rfl⟩
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at ht
    obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes a g _ _).1 ht
    cases hy
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hx
    obtain ⟨tag, pl, -, rfl⟩ := (poll_outcomes a g _ _).1 hx
    obtain ⟨z, hz⟩ := hk x
    rw [hz] at hkv
    obtain ⟨rfl, rfl⟩ := mem_pure.1 hkv
    exact ⟨tag, pl, mul_one _, z, rfl⟩

theorem routeVal_pure (K : Nat) (j : Fin (K + 1)) (v : value Bit ⊕ value State) :
    ∃ z, routeVal K j v = pure z := by
  rcases v with b | y <;> exact ⟨_, rfl⟩

theorem relayRouteVal_pure (K : Nat) (j₁ j₂ : Fin (K + 1)) (v : value Bit ⊕ value State) :
    ∃ z, relayRouteVal K j₁ j₂ v = pure z := by
  rcases v with b | y <;> exact ⟨_, rfl⟩

/-- With one common label, every request of every complete run carries it. -/
theorem relay_labels (q p : Poll) (l : Bool) (hq : q.label = l) (hp : p.label = l) (i : Fin (K + 2))
    (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ relayObservations K q.program p.program j i g) :
    ∀ e ∈ FreeMonoid.toList obs.2, e.label = l := by
  have key : ∀ (i : Fin (K + 2)) (g : Bool) (y : Except Bool (value Bit ⊕ value (States (K + 1))))
      (w : Word), (y, w) ∈ (relayStepM K q.program p.program j (injVal (K + 1) i (Sum.inl (bit g)))).outcomes →
      ∃ tag pl, w = FreeMonoid.of (event l g (tag, pl)) ∧ ∃ z, y = .ok z := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro g y w hm
      rw [relay_step_zero] at hm
      obtain ⟨tag, pl, hw, hz⟩ := poll_bind_outcome q g _ (relayRouteVal_pure (K + 1) 0 j.succ) hm
      exact ⟨tag, pl, hq ▸ hw, hz⟩
    · intro g y w hm
      rw [relay_step_succ] at hm
      obtain ⟨tag, pl, hw, hz⟩ := poll_bind_outcome p g _ (routeVal_pure (K + 1) 0) hm
      exact ⟨tag, pl, hp ▸ hw, hz⟩
  rw [relay_obs_eq] at h
  refine iter_induction (relayStepM K q.program p.program j)
    (fun _ => {obs | ∀ e ∈ FreeMonoid.toList obs.2, e.label = l}) ?_ ?_ ?_ _ h
  · intro v t' w hw
    obtain ⟨i, s, rfl⟩ := injVal_cases (K + 1) v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, -, z, hz⟩ := key i g _ _ hw
    cases hz
  · intro v b w hw
    obtain ⟨i, s, rfl⟩ := injVal_cases (K + 1) v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, rfl, -⟩ := key i g _ _ hw
    intro e he
    have : e = event l g (tag, pl) := by simpa using he
    rw [this]
    rfl
  · intro v next u r v' hu hv
    obtain ⟨i, s, rfl⟩ := injVal_cases (K + 1) v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, rfl, -⟩ := key i g _ _ hu
    intro e he
    have cases : e = event l g (tag, pl) ∨ e ∈ FreeMonoid.toList v' := by simpa using he
    rcases cases with rfl | tail
    · rfl
    · exact hv e tail

/-- The relaying state repeats into the block, where the second poll returns. -/
theorem relay_witness (q p : Poll) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (!q.returnRight, s)) *
      FreeMonoid.of (event p.label s (p.returnRight, c))) ∈
      relayObservations 0 q.program p.program 0 0 g := by
  rw [relay_obs_eq, iter_unfold]
  refine .inr (.inr ⟨injVal (0 + 1) (Fin.succ 0) (Sum.inl (bit s)), _, _, ?_, ?_, rfl⟩)
  · rw [relay_step_zero, Tagged.mem_bind]
    refine .inr ⟨Sum.inr (Sum.inl (bit s)), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes q g _ _).2 ⟨!q.returnRight, s, by rw [flag_not]; rfl, rfl⟩
  · rw [iter_unfold]
    refine .inr (.inl ⟨bit c, rfl, ?_⟩)
    rw [relay_step_succ, Tagged.mem_bind]
    refine .inr ⟨Sum.inl (bit c), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes p s _ _).2 ⟨p.returnRight, c, by rw [flag_self]; rfl, rfl⟩

/-- The relaying state can also repeat into itself before entering the block. -/
theorem relay_self_witness (q p : Poll) (g s s' c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (q.returnRight, s)) *
      (FreeMonoid.of (event q.label s (!q.returnRight, s')) *
        FreeMonoid.of (event p.label s' (p.returnRight, c)))) ∈
      relayObservations 0 q.program p.program 0 0 g := by
  rw [relay_obs_eq, iter_unfold]
  refine .inr (.inr ⟨injVal (0 + 1) 0 (Sum.inl (bit s)), _, _, ?_, ?_, rfl⟩)
  · rw [relay_step_zero, Tagged.mem_bind]
    refine .inr ⟨Sum.inl (bit s), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes q g _ _).2 ⟨q.returnRight, s, by rw [flag_self]; rfl, rfl⟩
  · rw [← relay_obs_eq]
    exact relay_witness q p s s' c

theorem relay_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label) :
    ¬ WithGuardedTablePacking.WithPhaseUniformity.Eqv false [State]
      (relayFan 0 q.program p'.program 0 0) (relayFan 0 q.program p.program 0 0) [Bit] := by
  intro e
  have eq := WithGuardedTablePacking.WithPhaseUniformity.Eqv.sound false J M (fun _ _ => ⟨rfl, rfl⟩) e
    (relayFan_typed 0 q.program p'.program 0 0).hasType (relayFan_typed 0 q.program p.program 0 0).hasType
  have obs : relayObservations 0 q.program p'.program 0 0 false =
      relayObservations 0 q.program p.program 0 0 false := by
    unfold relayObservations denoteSingletonRegion
    rw [eq]
  have mem := relay_witness q p' false false false
  rw [obs] at mem
  exact other (relay_labels 0 0 q p p.label same rfl 0 false mem
    (event p'.label false (p'.returnRight, false)) (by simp))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
