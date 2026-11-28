module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterModel

/-! # Router tables in any coherent trace model

The computations of `TableModel` and `RouterModel`, for an arbitrary
instruction model on the ordered-trace monad. They are used with the
request-prefix model.
-/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterRun

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
local notation "PEqv" => WithGuardedTablePacking.WithPhaseUniformity.Eqv
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "Lit" => ofRegion N

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel (idBr brOf lit_inl lit_inr)

set_option backward.isDefEq.respectTransparency false

section Coherent

-- The instruction interpretation is the parameter of this section.
set_option linter.concreteInstances false

variable [inst : InstructionModel J M signature.Instr] [RegionTypingCoherent (Φ := signature.Instr) J M]

theorem comp_run {A B D : Ty Empty} (f : ofType N A ⟶ ofType N B) (g : ofType N B ⟶ ofType N D)
    (x : value A) :
    (((F).map (f ≫ g)).of x : Trace (value D)) =
      Bind.bind (m := Trace) (((F).map f).of x : Trace (value B)) (fun y => ((F).map g).of y) := by
  let u : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj B) := (F).map f
  let c : (J).obj ((M).obj B) ⟶ (J).obj ((M).obj D) := (F).map g
  have comp : (F).map (f ≫ g) = u ≫ c := (F).map_comp _ _
  exact (congrArg (fun h : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj D) => h.of x) comp).trans
    (congrFun (Kleisli.Type.comp_of_eq_kleisliRight Trace u c) x)

theorem lit_run {A B : Ty Empty} {r : Region signature.Instr} (hr : ValueBranches [A] r [B]) :
    (F).map (Lit hr) = denoteSingletonRegion J M hr.hasType :=
  Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩)
    (WithGuardedTablePacking.seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩)) hr

theorem id_run (A : Ty Empty) (x : value A) :
    (((F).map (Lit (idBr A))).of x : Trace (value A)) = (pure x : Trace (value A)) := by
  have eq : Lit (idBr A) = 𝟙 (ofType N A) :=
    (congrArg (Paper.Extension.Singleton.projection N).map (Paper.TypeCategory.ofRegion_id (Φ := signature.Instr) A)).trans
      ((Paper.Extension.Singleton.projection N).map_id _)
  rw [eq, (F).map_id]
  rfl

theorem inl_run {X A B : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t A) (x : value X) :
    (((F).map (Lit (brOf (A := Silmaril.coprod A B) (.inl ht)))).of x : Trace (value A ⊕ value B)) =
      Bind.bind (m := Trace) (((F).map (Lit (brOf ht))).of x : Trace (value A))
        (fun a => pure (Sum.inl a)) := by
  rw [lit_inl ht]
  exact (comp_run _ _ x).trans (congrArg _ (funext fun a => inl_of (A := B) (B := A) a))

theorem inr_run {X A B : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t B) (x : value X) :
    (((F).map (Lit (brOf (A := Silmaril.coprod A B) (.inr ht)))).of x : Trace (value A ⊕ value B)) =
      Bind.bind (m := Trace) (((F).map (Lit (brOf ht))).of x : Trace (value B))
        (fun b => pure (Sum.inr b)) := by
  rw [lit_inr ht]
  exact (comp_run _ _ x).trans (congrArg _ (funext fun b => inr_of (A := B) (B := A) b))

/-- The constructor entry is the injection of values. -/
theorem inj_run : ∀ (K : Nat) (j : Fin (K + 1)) (s : value State),
    (((F).map (Lit (entry_typed K j))).of s : Trace (value (States K))) =
      (pure (injVal K j s) : Trace (value (States K)))
  | 0, j, s => id_run State s
  | K + 1, j, s => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (inl_run (B := States K) (.var (i := 0) rfl) s).trans
        ((congrArg (Bind.bind (m := Trace) · _) (id_run State s)).trans (pure_bind _ _))
    · exact (inr_run (A := State) (injTm_typed (.var (i := 0) rfl) K j) s).trans
        ((congrArg (Bind.bind (m := Trace) · _) (inj_run K j s)).trans (pure_bind _ _))

theorem dispatch_run {D : Ty Empty} (K : Nat) {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [D]) (i : Fin (K + 1)) (s : value State) :
    (((F).map (Lit (dispatch_typed K h))).of (injVal K i s) : Trace (value D)) =
      ((F).map (Lit (h i))).of s := by
  have arrow : Lit (entry_typed K i) ≫ Lit (dispatch_typed K h) = Lit (h i) :=
    ((Paper.Extension.Singleton.projection N).map_comp _ _).symm.trans (congrArg (Paper.Extension.Singleton.projection N).map (Tables.inj_dispatch K h i))
  have run := comp_run (Lit (entry_typed K i)) (Lit (dispatch_typed K h)) s
  rw [arrow, inj_run, pure_bind] at run
  exact run.symm

theorem inj_of_run {X : Ty Empty} {a : Tm signature.Instr} (ha : Tm.BranchValue [X] a State)
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
        ((congrArg (Bind.bind (m := Trace) · _) (inj_of_run ha v base K j x)).trans (pure_bind _ _))

/-- The entered loop of any dispatched rows is the interpreter's iterator
on the dispatcher step. -/
theorem dispatch_obs_eq {K : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)]) (i : Fin (K + 1)) (g : Bool) :
    ((denoteSingletonRegion J M (dispatchEntered_typed h i).hasType).of (Sum.inl (bit g))).outcomes =
      (Silmaril.Elgot.iter (m := Trace)
        (fun v => (denoteSingletonRegion J M (dispatch_typed K h).hasType).of v)
        (injVal K i (Sum.inl (bit g)))).outcomes := by
  have arrow : Lit (dispatchEntered_typed h i) = Lit (entry_typed K i) ≫ Lit (dispatchLoop_typed h) :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (entry_typed K i) (dispatchLoop_typed h)
        (dispatchEntered_typed h i)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  have run := comp_run (Lit (entry_typed K i)) (Lit (dispatchLoop_typed h)) (Sum.inl (bit g))
  rw [← arrow, inj_run, pure_bind] at run
  have lhs := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) =>
    k.of (Sum.inl (bit g))) (lit_run (dispatchEntered_typed h i))
  have rhs := congrArg (fun k : (J).obj ((M).obj (States K)) ⟶ (J).obj ((M).obj Bit) =>
    k.of (injVal K i (Sum.inl (bit g)))) (lit_run (dispatchLoop_typed h))
  have loop : (denoteSingletonRegion J M (dispatchLoop_typed h).hasType).of (injVal K i (Sum.inl (bit g))) =
      Silmaril.Elgot.iter (m := Trace)
        (fun v => (denoteSingletonRegion J M (dispatch_typed K h).hasType).of v)
        (injVal K i (Sum.inl (bit g))) := by
    refine (iterate_run (dispatch_typed K h) _).trans ?_
    rw [lit_run (dispatch_typed K h)]
    rfl
  exact congrArg Tagged.outcomes (lhs.symm.trans (run.trans (rhs.trans loop)))

theorem bitTm_run (c : Bool) (u : value Ty.unit) :
    (((F).map (Lit (brOf (bitTm_typed c)))).of u : Trace (value Bit)) = (pure (bit c) : Trace (value Bit)) := by
  cases c
  · exact (inl_run (B := Ty.unit) (.var (i := 0) rfl) u).trans
      ((congrArg (Bind.bind (m := Trace) · _) (id_run Ty.unit u)).trans (pure_bind _ _))
  · exact (inr_run (A := Ty.unit) (.var (i := 0) rfl) u).trans
      ((congrArg (Bind.bind (m := Trace) · _) (id_run Ty.unit u)).trans (pure_bind _ _))

theorem bitState_const_run (q : Bool) (u : value Ty.unit) :
    (((F).map (Lit (brOf (A := State) (.inl (bitTm_typed q))))).of u : Trace (value State)) =
      (pure (Sum.inl (bit q)) : Trace (value State)) :=
  (inl_run (B := packedExitType ([] : LCtx (Ty Empty))) (bitTm_typed q) u).trans
    ((congrArg (Bind.bind (m := Trace) · _) (bitTm_run q u)).trans (pure_bind _ _))

theorem act_run (K : Nat) (a : Act K) (u : value Ty.unit) :
    (((F).map (Lit (act_typed K a))).of u : Trace (value Bit ⊕ value (States K))) =
      (pure (actVal K a) : Trace (value Bit ⊕ value (States K))) := by
  cases a with
  | ret c =>
    exact (inl_run (B := States K) (bitTm_typed c) u).trans
      ((congrArg (Bind.bind (m := Trace) · _) (bitTm_run c u)).trans (pure_bind _ _))
  | go j q =>
    exact (inr_run (A := Bit) (injTm_typed (.inl (bitTm_typed q)) K j) u).trans
      ((congrArg (Bind.bind (m := Trace) · _)
        (inj_of_run (.inl (bitTm_typed q)) (fun _ => Sum.inl (bit q)) (bitState_const_run q) K j u)).trans
          (pure_bind _ _))

theorem bitSplit_run (K : Nat) (a₀ a₁ : Act K) (b : value Bit) :
    (((F).map (Lit (bitSplit_typed K a₀ a₁))).of b : Trace (value Bit ⊕ value (States K))) =
      (pure (actVal K (Sum.elim (fun _ => a₀) (fun _ => a₁) b)) : Trace (value Bit ⊕ value (States K))) := by
  have arrow : Lit (bitSplit_typed K a₀ a₁) = exactCopair N (Lit (act_typed K a₀)) (Lit (act_typed K a₁)) :=
    (exactCopair_ofRegion N (act_typed K a₀) (act_typed K a₁)).symm
  rw [arrow]
  rcases b with u | u
  · exact (copair_inl_of _ _ u).trans (act_run K a₀ u)
  · exact (copair_inr_of _ _ u).trans (act_run K a₁ u)

theorem routerRoute_run (K : Nat) (a : Bool → Bool → Act K) (v : value Bit ⊕ value State) :
    (((F).map (Lit (routerRoute_typed K a))).of v : Trace (value Bit ⊕ value (States K))) =
      routerRouteVal K a v := by
  have arrow : Lit (routerRoute_typed K a) =
      exactCopair N (Lit (bitSplit_typed K (a false false) (a false true)))
        (Lit (stateSplit_typed K (a true false) (a true true))) :=
    (exactCopair_ofRegion N (bitSplit_typed K (a false false) (a false true))
      (stateSplit_typed K (a true false) (a true true))).symm
  have inner : Lit (stateSplit_typed K (a true false) (a true true)) =
      exactCopair N (Lit (bitSplit_typed K (a true false) (a true true))) (Lit (dead_typed K)) :=
    (exactCopair_ofRegion N (bitSplit_typed K (a true false) (a true true)) (dead_typed K)).symm
  rw [arrow]
  rcases v with b | s
  · refine (copair_inl_of _ _ b).trans ((bitSplit_run K _ _ b).trans ?_)
    rcases b with u | u <;> rfl
  · refine (copair_inr_of _ _ s).trans ?_
    rw [inner]
    rcases s with b | e
    · refine (copair_inl_of _ _ b).trans ((bitSplit_run K _ _ b).trans ?_)
      rcases b with u | u <;> rfl
    · exact e.elim

theorem routerRow_run (K : Nat) (p : Program) (a : Bool → Bool → Act K) (s : value State) :
    (((F).map (Lit (routerRow_typed K p a))).of s : Trace (value Bit ⊕ value (States K))) =
      Bind.bind (m := Trace) (stepIn p s) (routerRouteVal K a) := by
  have arrow : Lit (routerRow_typed K p a) = stepArrow p ≫ Lit (routerRoute_typed K a) :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (step_typed p) (routerRoute_typed K a) (routerRow_typed K p a)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  rw [arrow]
  exact (comp_run _ _ s).trans
    (congr (congrArg (Bind.bind (m := Trace)) (step_run_in p s)) (funext (routerRoute_run K a)))

/-- One step of a router table at state `i`, in any such model. -/
theorem router_step_run_in {K : Nat} (t : Router K) (i : Fin (K + 1)) (s : value State) :
    (denoteSingletonRegion J M (dispatch_typed K t.rows_typed).hasType).of (injVal K i s) =
      Bind.bind (m := Trace) (stepIn (t.prog i) s) (routerRouteVal K (t.act i)) := by
  have rows := dispatch_run K t.rows_typed i s
  have literal := congrArg (fun h : (J).obj ((M).obj (States K)) ⟶ (J).obj ((M).obj _) =>
    h.of (injVal K i s)) (lit_run (dispatch_typed K t.rows_typed))
  exact literal.symm.trans (rows.trans (routerRow_run K (t.prog i) (t.act i) s))

end Coherent

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterRun
