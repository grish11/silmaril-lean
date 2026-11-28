module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SwitchTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableKeys

/-! # Switch tables in the four-reply interpreter -/

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

noncomputable local instance switchInstructions : InstructionModel J M signature.Instr := instructions model
local instance switchCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

/-! ## Routing on values -/

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

theorem falseState_run (u : value Ty.unit) :
    (((F).map (Lit (brOf (A := State) (.inl (.inl (.var (i := 0) rfl)))))).of u : Trace (value State)) =
      (pure (Sum.inl (Sum.inl u)) : Trace (value State)) :=
  (inl_run (B := packedExitType ([] : LCtx (Ty Empty))) (.inl (.var (i := 0) rfl)) u).trans
    ((congrArg (Bind.bind (m := Trace) · _)
      ((inl_run (B := Ty.unit) (.var (i := 0) rfl) u).trans
        ((congrArg (Bind.bind (m := Trace) · _) (id_run Ty.unit u)).trans (pure_bind _ _)))).trans
      (pure_bind _ _))

theorem bitRoute_run (K : Nat) (j : Fin (K + 1)) (b : value Bit) :
    (((F).map (Lit (bitRoute_typed K j))).of b : Trace (value Bit ⊕ value (States K))) =
      switchRouteVal K j j (Sum.inl b) := by
  have arrow : Lit (bitRoute_typed K j) = exactCopair N (Lit (hold_typed K j)) (Lit (leave_typed K)) :=
    (exactCopair_ofRegion N (hold_typed K j) (leave_typed K)).symm
  rw [arrow]
  rcases b with u | u
  · exact (copair_inl_of _ _ u).trans
      ((inr_run (A := Bit) (injTm_typed (.inl (.inl (.var (i := 0) rfl))) K j) u).trans
        ((congrArg (Bind.bind (m := Trace) · _)
          (inj_of_run (.inl (.inl (.var (i := 0) rfl))) (fun u => Sum.inl (Sum.inl u)) falseState_run K j u)).trans
            (pure_bind _ _)))
  · exact (copair_inr_of _ _ u).trans
      ((inl_run (B := States K) (.inr (.var (i := 0) rfl)) u).trans
        ((congrArg (Bind.bind (m := Trace) · _)
          ((inr_run (A := Ty.unit) (.var (i := 0) rfl) u).trans
            ((congrArg (Bind.bind (m := Trace) · _) (id_run Ty.unit u)).trans (pure_bind _ _)))).trans
          (pure_bind _ _)))

theorem switchRoute_run (K : Nat) (j₀ j₁ : Fin (K + 1)) (v : value Bit ⊕ value State) :
    (((F).map (Lit (switchRoute_typed K j₀ j₁))).of v : Trace (value Bit ⊕ value (States K))) =
      switchRouteVal K j₀ j₁ v := by
  have arrow : Lit (switchRoute_typed K j₀ j₁) =
      exactCopair N (Lit (bitRoute_typed K j₀)) (Lit (goto_typed K j₁)) :=
    (exactCopair_ofRegion N (bitRoute_typed K j₀) (goto_typed K j₁)).symm
  rw [arrow]
  rcases v with b | y
  · refine (copair_inl_of _ _ b).trans ((bitRoute_run K j₀ b).trans ?_)
    rcases b with u | u <;> rfl
  · exact (copair_inr_of _ _ y).trans
      ((inr_run (A := Bit) (injTm_typed (.var (i := 0) rfl) K j₁) y).trans
        ((congrArg (Bind.bind (m := Trace) · _) (inj_run K j₁ y)).trans (pure_bind _ _)))

theorem switchRow_run (K : Nat) (p : Program) (j₀ j₁ : Fin (K + 1)) (s : value State) :
    (((F).map (Lit (switchRow_typed K p j₀ j₁))).of s : Trace (value Bit ⊕ value (States K))) =
      Bind.bind (m := Trace) (stepModel p s) (switchRouteVal K j₀ j₁) := by
  have arrow : Lit (switchRow_typed K p j₀ j₁) = stepArrow p ≫ Lit (switchRoute_typed K j₀ j₁) :=
    (congrArg (Paper.Extension.Singleton.projection N).map (Tables.switchRow_arrow K p j₀ j₁)).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  rw [arrow]
  exact (comp_run _ _ s).trans
    (congr (congrArg (Bind.bind (m := Trace)) (BitLoop.step_run p s)) (funext (switchRoute_run K j₀ j₁)))

/-- One step of the table at state `i`. -/
theorem switch_step_run {K : Nat} (t : Switch K) (i : Fin (K + 1)) (s : value State) :
    t.stepM (injVal K i s) =
      Bind.bind (m := Trace) (stepModel (t.prog i) s) (switchRouteVal K (t.next i false) (t.next i true)) := by
  have rows := dispatch_run K t.rows_typed i s
  have literal := congrArg (fun h : (J).obj ((M).obj (States K)) ⟶ (J).obj ((M).obj _) =>
    h.of (injVal K i s)) (lit_run (dispatch_typed K t.rows_typed))
  exact literal.symm.trans (rows.trans (switchRow_run K (t.prog i) (t.next i false) (t.next i true) s))

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

theorem switch_obs_eq {K : Nat} (t : Switch K) (i : Fin (K + 1)) (g : Bool) :
    t.observations i g =
      (Silmaril.Elgot.iter (m := Trace) t.stepM (injVal K i (Sum.inl (bit g)))).outcomes :=
  dispatch_obs_eq t.rows_typed i g

/-! ## One round of a table of polls -/

theorem route_cases (K : Nat) (j₀ j₁ : Fin (K + 1)) (rr tag pl : Bool)
    {y : Except Bool (value Bit ⊕ value (States K))} {v : Word}
    (hk : (y, v) ∈ (switchRouteVal K j₀ j₁ (terminal (if tag then !rr else rr) pl)).outcomes) :
    v = 1 ∧ ((tag = rr ∧ pl = true ∧ y = .ok (.inl (bit true))) ∨
      (tag = rr ∧ pl = false ∧ y = .ok (.inr (injVal K j₀ (.inl (bit false))))) ∨
      (tag = !rr ∧ y = .ok (.inr (injVal K j₁ (.inl (bit pl)))))) := by
  cases tag <;> cases rr <;> cases pl <;> obtain ⟨rfl, rfl⟩ := mem_pure.1 hk <;>
    first
    | exact ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩
    | exact ⟨rfl, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩
    | exact ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩

theorem route_leave (K : Nat) (j₀ j₁ : Fin (K + 1)) (rr : Bool) :
    (Except.ok (Sum.inl (bit true)), (1 : Word)) ∈
      (switchRouteVal K j₀ j₁ (terminal (if rr then !rr else rr) true)).outcomes := by
  rw [flag_self]
  exact mem_pure.2 ⟨rfl, rfl⟩

theorem route_hold (K : Nat) (j₀ j₁ : Fin (K + 1)) (rr : Bool) :
    (Except.ok (Sum.inr (injVal K j₀ (Sum.inl (bit false)))), (1 : Word)) ∈
      (switchRouteVal K j₀ j₁ (terminal (if rr then !rr else rr) false)).outcomes := by
  rw [flag_self]
  exact mem_pure.2 ⟨rfl, rfl⟩

theorem route_repeat (K : Nat) (j₀ j₁ : Fin (K + 1)) (rr pl : Bool) :
    (Except.ok (Sum.inr (injVal K j₁ (Sum.inl (bit pl)))), (1 : Word)) ∈
      (switchRouteVal K j₀ j₁ (terminal (if !rr then !rr else rr) pl)).outcomes := by
  rw [flag_not]
  exact mem_pure.2 ⟨rfl, rfl⟩

variable {K : Nat} (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Bool → Fin (K + 1))

/-- A round has one event. Its reply decides between leaving and the two
successors. -/
theorem switch_step_cases (i : Fin (K + 1)) (g : Bool) {y : Except Bool (value Bit ⊕ value (States K))}
    {w : Word} (hm : (y, w) ∈ ((Switch.ofPolls poll next).stepM (injVal K i (Sum.inl (bit g)))).outcomes) :
    ∃ tag pl, w = FreeMonoid.of (event (poll i).label g (tag, pl)) ∧
      ((tag = (poll i).returnRight ∧ pl = true ∧ y = .ok (.inl (bit true))) ∨
        (tag = (poll i).returnRight ∧ pl = false ∧
          y = .ok (.inr (injVal K (next i false) (.inl (bit false))))) ∨
        (tag = !(poll i).returnRight ∧ y = .ok (.inr (injVal K (next i true) (.inl (bit pl)))))) := by
  rw [switch_step_run, Tagged.mem_bind] at hm
  rcases hm with ⟨t', rfl, ht⟩ | ⟨x, u, v, hx, hk, rfl⟩
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at ht
    obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes (poll i) g _ _).1 ht
    cases hy
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hx
    obtain ⟨tag, pl, hy, rfl⟩ := (poll_outcomes (poll i) g _ _).1 hx
    cases hy
    obtain ⟨rfl, cases⟩ := route_cases K (next i false) (next i true) (poll i).returnRight tag pl hk
    exact ⟨tag, pl, mul_one _, cases⟩

theorem switch_step_mem (i : Fin (K + 1)) (g tag pl : Bool)
    {y : Except Bool (value Bit ⊕ value (States K))}
    (hk : (y, (1 : Word)) ∈ (switchRouteVal K (next i false) (next i true)
      (terminal (if tag then !(poll i).returnRight else (poll i).returnRight) pl)).outcomes) :
    (y, FreeMonoid.of (event (poll i).label g (tag, pl))) ∈
      ((Switch.ofPolls poll next).stepM (injVal K i (Sum.inl (bit g)))).outcomes := by
  rw [switch_step_run, Tagged.mem_bind]
  refine .inr ⟨_, _, 1, ?_, hk, mul_one _⟩
  rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
  exact (poll_outcomes (poll i) g _ _).2 ⟨tag, pl, rfl, rfl⟩

/-- The observation law: a complete run leaves after one request, or
continues at one of the two successors after its first request. -/
theorem switch_unfold (i : Fin (K + 1)) (g : Bool) (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Switch.ofPolls poll next).observations i g ↔
      (r = .ok (bit true) ∧ w = FreeMonoid.of (event (poll i).label g ((poll i).returnRight, true))) ∨
      (∃ v, (r, v) ∈ (Switch.ofPolls poll next).observations (next i false) false ∧
        w = FreeMonoid.of (event (poll i).label g ((poll i).returnRight, false)) * v) ∨
      (∃ pl v, (r, v) ∈ (Switch.ofPolls poll next).observations (next i true) pl ∧
        w = FreeMonoid.of (event (poll i).label g (!(poll i).returnRight, pl)) * v) := by
  simp only [switch_obs_eq]
  rw [iter_unfold]
  constructor
  · rintro (⟨t', -, ht⟩ | ⟨b, rfl, hb⟩ | ⟨nxt, u, v, hu, hv, rfl⟩)
    · obtain ⟨tag, pl, -, c⟩ := switch_step_cases poll next i g ht
      rcases c with ⟨-, -, e⟩ | ⟨-, -, e⟩ | ⟨-, e⟩ <;> cases e
    · obtain ⟨tag, pl, rfl, c⟩ := switch_step_cases poll next i g hb
      rcases c with ⟨rfl, rfl, e⟩ | ⟨-, -, e⟩ | ⟨-, e⟩
      · cases e
        exact .inl ⟨rfl, rfl⟩
      · cases e
      · cases e
    · obtain ⟨tag, pl, rfl, c⟩ := switch_step_cases poll next i g hu
      rcases c with ⟨-, -, e⟩ | ⟨rfl, rfl, e⟩ | ⟨rfl, e⟩
      · cases e
      · cases e
        exact .inr (.inl ⟨v, hv, rfl⟩)
      · cases e
        exact .inr (.inr ⟨pl, v, hv, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨pl, v, hv, rfl⟩)
    · exact .inr (.inl ⟨bit true, rfl, switch_step_mem poll next i g _ true (route_leave K _ _ _)⟩)
    · exact .inr (.inr ⟨_, _, v, switch_step_mem poll next i g _ false (route_hold K _ _ _), hv, rfl⟩)
    · exact .inr (.inr ⟨_, _, v, switch_step_mem poll next i g _ pl (route_repeat K _ _ _ pl), hv, rfl⟩)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
