module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Entry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterPrefix

/-! # Literal request trees are determined by one constant entry

In the request-prefix model, the observations of a table of literal
request trees entered with one constant determine its entered loop.
-/

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
local notation "PEqv" => WithGuardedTablePacking.WithPhaseUniformity.Eqv
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "Lit" => ofRegion N
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix
open Paper.WithCaseBind.BitQuery (request)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Answer)

set_option backward.isDefEq.respectTransparency false

section Point

noncomputable local instance pointInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance pointCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

theorem valid_denote {X D : Ty Empty} {r r' : Region signature.Instr} (h : ValueBranches [X] r [D])
    (h' : ValueBranches [X] r' [D]) (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) :
    denoteSingletonRegion J M h.hasType = denoteSingletonRegion J M h'.hasType := by
  have eq := v J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold denoteSingletonRegion
  rw [eq]

/-- A region entered with a constant state runs the region on that state. -/
theorem const_denote {D : Ty Empty} {r : Region signature.Instr} (h : ValueBranches [State] r [D]) (q : Bool)
    (u : value Ty.unit) :
    (denoteSingletonRegion J M (constEntry_typed q h).hasType).of u =
      (denoteSingletonRegion J M h.hasType).of (Sum.inl (bit q)) := by
  have arrow : Lit (constEntry_typed q h) = Lit (const_typed q) ≫ Lit h :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (const_typed q) h (constEntry_typed q h)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  have run := RouterRun.comp_run (Lit (const_typed q)) (Lit h) u
  rw [← arrow] at run
  have c := RouterRun.bitState_const_run q u
  have lhs := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj D) => k.of u)
    (RouterRun.lit_run (constEntry_typed q h))
  have rhs := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj D) => k.of (Sum.inl (bit q)))
    (RouterRun.lit_run h)
  exact lhs.symm.trans (run.trans (((congrArg (Bind.bind (m := Trace) · _) c).trans (pure_bind _ _)).trans rhs))

variable {K K' : Nat}

/-- Two tables of literal request trees with the same observations at one
constant entry have equal entered loops. -/
theorem ltable_point (t : LTable K) (t' : LTable K') (x : Fin (K + 1)) (x' : Fin (K' + 1)) (q : Bool)
    (obs : ((denoteSingletonRegion J M (t.entered_typed x).hasType).of (Sum.inl (bit q))).outcomes =
      ((denoteSingletonRegion J M (t'.entered_typed x').hasType).of (Sum.inl (bit q))).outcomes) :
    PEqv false [State] (t.entered x) (t'.entered x') [Bit] := by
  obtain ⟨_, label, act, e, E⟩ := t.exists_router
  obtain ⟨_, label', act', e', E'⟩ := t'.exists_router
  have d := valid_denote (t.entered_typed x) ((Router.ofLabels label act).entered_typed (e x))
    (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (E x) _ _)
  have d' := valid_denote (t'.entered_typed x') ((Router.ofLabels label' act').entered_typed (e' x'))
    (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (E' x') _ _)
  have o : (Router.ofLabels label act).prefixObservations (e x) q =
      (Router.ofLabels label' act').prefixObservations (e' x') q := by
    unfold Router.prefixObservations
    rw [← d, ← d']
    exact obs
  exact (E x).trans ((router_eqv_of_bisim label act label' act'
    (fun a b => ∃ g, (Router.ofLabels label act).prefixObservations a g =
      (Router.ofLabels label' act').prefixObservations b g)
    (fun a b ⟨g, h⟩ => prefix_label label act label' act' a b g g h)
    (fun a b ⟨g, h⟩ tag pl => prefix_act_rel label act label' act' a b g
      (prefix_label label act label' act' a b g g h) h tag pl) (e x) (e' x') ⟨q, o⟩).trans (E' x').symm)

variable {r r' : Region signature.Instr} {t : Bool → LTable K} {x : Bool → Fin (K + 1)}
  {t' : Bool → LTable K'} {x' : Bool → Fin (K' + 1)}

/-- Valid loops that are literal sources at each constant have equal
sources at each constant. -/
theorem pointed_sources (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : Pointed r t x) (hp' : Pointed r' t' x')
    (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) (q : Bool) :
    PEqv false [State] ((t q).entered (x q)) ((t' q).entered (x' q)) [Bit] := by
  have u : value Ty.unit := ()
  have a := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (valid_denote (constEntry_typed q h) (constEntry_typed q ((t q).entered_typed (x q)))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hp q) _ _))
  have a' := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (valid_denote (constEntry_typed q h') (constEntry_typed q ((t' q).entered_typed (x' q)))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hp' q) _ _))
  have m := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) => k.of (Sum.inl (bit q)))
    (valid_denote h h' v)
  exact ltable_point (t q) (t' q) (x q) (x' q) q (congrArg Tagged.outcomes
    ((const_denote ((t q).entered_typed (x q)) q u).symm.trans (a.symm.trans
      ((const_denote h q u).trans (m.trans ((const_denote h' q u).symm.trans
        (a'.trans (const_denote ((t' q).entered_typed (x' q)) q u))))))))

end Point

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
