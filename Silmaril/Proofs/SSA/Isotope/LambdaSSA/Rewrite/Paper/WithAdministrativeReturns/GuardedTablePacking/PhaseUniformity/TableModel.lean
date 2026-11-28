module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.RoundsModel

/-! # Multi-state tables in the four-reply interpreter -/

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
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases (inl_rep inr_rep)

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "Lit" => ofRegion N

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

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

theorem idBr (A : Ty Empty) : ValueBranches [A] (.br 0 (.var 0) : Region signature.Instr) [A] :=
  .br rfl (.var rfl)

theorem brOf {X A : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t A) :
    ValueBranches [X] (.br 0 t : Region signature.Instr) [A] :=
  .br rfl ht

theorem id_run (A : Ty Empty) (x : value A) :
    (((F).map (Lit (idBr A))).of x : Trace (value A)) = (pure x : Trace (value A)) := by
  have eq : Lit (idBr A) = 𝟙 (ofType N A) :=
    (congrArg (Paper.Extension.Singleton.projection N).map (Paper.TypeCategory.ofRegion_id (Φ := signature.Instr) A)).trans
      ((Paper.Extension.Singleton.projection N).map_id _)
  rw [eq, (F).map_id]
  rfl

theorem lit_inl {X A B : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t A) :
    Lit (brOf (A := Silmaril.coprod A B) (.inl ht)) = Lit (brOf ht) ≫ (sumCofan N A B).inl := by
  have rep : coprod.inl ≫ (Paper.TypeCategory.sumIso (Φ := signature.Instr) A B).inv =
      (Paper.TypeCategory.sumCofan A B).inl :=
    (Iso.comp_inv_eq _).2 (Paper.TypeCategory.sumCofan_inl_sumIso_hom A B).symm
  exact (congrArg (Paper.Extension.Singleton.projection N).map ((Tables.br_inl (B := B) ht).trans
    (congrArg (Paper.TypeCategory.ofRegion (brOf ht) ≫ ·) rep))).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)

theorem lit_inr {X A B : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t B) :
    Lit (brOf (A := Silmaril.coprod A B) (.inr ht)) = Lit (brOf ht) ≫ (sumCofan N A B).inr := by
  have rep : coprod.inr ≫ (Paper.TypeCategory.sumIso (Φ := signature.Instr) A B).inv =
      (Paper.TypeCategory.sumCofan A B).inr :=
    (Iso.comp_inv_eq _).2 (Paper.TypeCategory.sumCofan_inr_sumIso_hom A B).symm
  exact (congrArg (Paper.Extension.Singleton.projection N).map ((Tables.br_inr (A := A) ht).trans
    (congrArg (Paper.TypeCategory.ofRegion (brOf ht) ≫ ·) rep))).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)

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

theorem route_run (K : Nat) (j : Fin (K + 1)) (v : value Bit ⊕ value State) :
    (((F).map (Lit (route_typed K j))).of v : Trace (value Bit ⊕ value (States K))) = routeVal K j v := by
  have arrow : Lit (route_typed K j) = exactCopair N (Lit (ret_typed K)) (Lit (goto_typed K j)) :=
    (exactCopair_ofRegion N (ret_typed K) (goto_typed K j)).symm
  rw [arrow]
  rcases v with b | y
  · exact (copair_inl_of _ _ b).trans
      ((inl_run (B := States K) (.var (i := 0) rfl) b).trans
        ((congrArg (Bind.bind (m := Trace) · _) (id_run Bit b)).trans (pure_bind _ _)))
  · exact (copair_inr_of _ _ y).trans
      ((inr_run (A := Bit) (injTm_typed (.var (i := 0) rfl) K j) y).trans
        ((congrArg (Bind.bind (m := Trace) · _) (inj_run K j y)).trans (pure_bind _ _)))

/-- One step of the table at state `i`: the step of that row's program,
then routing to the row's successor. -/
theorem step_run {K : Nat} (t : Table K) (i : Fin (K + 1)) (s : value State) :
    t.stepM (injVal K i s) =
      Bind.bind (m := Trace) (stepModel (t.prog i) s) (routeVal K (t.next i)) := by
  have rows := dispatch_run K (fun i => row_typed K (t.prog i) (t.next i)) i s
  have arrow : Lit (row_typed K (t.prog i) (t.next i)) =
      stepArrow (t.prog i) ≫ Lit (route_typed K (t.next i)) :=
    (congrArg (Paper.Extension.Singleton.projection N).map (Tables.row_arrow K (t.prog i) (t.next i))).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  rw [arrow] at rows
  have literal := congrArg (fun h : (J).obj ((M).obj (States K)) ⟶ (J).obj ((M).obj _) =>
    h.of (injVal K i s)) (lit_run t.step_typed)
  exact literal.symm.trans (rows.trans ((comp_run _ _ s).trans
    (congr (congrArg (Bind.bind (m := Trace)) (BitLoop.step_run (t.prog i) s))
      (funext (route_run K (t.next i))))))

theorem loop_run {K : Nat} (t : Table K) (v : value (States K)) :
    (denoteSingletonRegion J M t.loop_typed.hasType).of v =
      Silmaril.Elgot.iter (m := Trace) t.stepM v := by
  refine (iterate_run t.step_typed v).trans ?_
  rw [lit_run t.step_typed]
  rfl

theorem observations_eq {K : Nat} (t : Table K) (i : Fin (K + 1)) (g : Bool) :
    t.observations i g =
      (Silmaril.Elgot.iter (m := Trace) t.stepM (injVal K i (Sum.inl (bit g)))).outcomes := by
  have arrow : Lit (t.entered_typed i) = Lit (entry_typed K i) ≫ Lit t.loop_typed :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (entry_typed K i) t.loop_typed (t.entered_typed i)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  have run := comp_run (Lit (entry_typed K i)) (Lit t.loop_typed) (Sum.inl (bit g))
  rw [← arrow, inj_run, pure_bind] at run
  have lhs := congrArg (fun h : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) =>
    h.of (Sum.inl (bit g))) (lit_run (t.entered_typed i))
  have rhs := congrArg (fun h : (J).obj ((M).obj (States K)) ⟶ (J).obj ((M).obj Bit) =>
    h.of (injVal K i (Sum.inl (bit g)))) (lit_run t.loop_typed)
  exact congrArg Tagged.outcomes (lhs.symm.trans (run.trans (rhs.trans (loop_run t _))))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
