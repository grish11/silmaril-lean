module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Thms

/-! # Validated model separation for canonical live selected syntax -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.OpenReplay
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply (Trace)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

private theorem pushEmit_normal {L : List (Ty Empty)} {n : Nat} (label : Bool) (p : ReadTree L n) :
    (CanonicalLive.pushEmit label p).witnessed.normal = .emit label p.witnessed.normal := by
  cases p <;> rfl

theorem witnessed_normal {L : List (Ty Empty)} {n : Nat} (p : CanonicalLive L n) :
    p.readTree.witnessed.normal = p.normal := by
  induction p with
  | ret => rfl
  | emit label next ih =>
    rw [CanonicalLive.readTree, pushEmit_normal, ih]
    rfl
  | request _ _ _ hl hr =>
    simp [CanonicalLive.readTree, ReadTree.witnessed, Finite.Tree.normal, CanonicalLive.normal, hl, hr]
  | guard _ _ _ _ _ _ hfl hfr htl htr =>
    simp [CanonicalLive.readTree, ReadTree.witnessed, Finite.Tree.normal, CanonicalLive.normal, hfl, hfr, htl, htr]

private theorem projection_injective {n : Nat} {i j : Fin n}
    (same : (fun env : Finite.Assignment n => env i) = (fun env => env j)) : i = j := by
  have probe := congrFun same (fun k => decide (k = i))
  exact (of_decide_eq_true (probe.symm.trans (by simp))).symm

theorem normal_injective {L : List (Ty Empty)} {n : Nat} :
    Function.Injective (@CanonicalLive.normal L n) := by
  intro p
  induction p with
  | ret exit slot =>
    intro q eq
    cases q with
    | ret other j =>
      obtain ⟨rfl, same⟩ := Finite.Normal.ret.inj eq
      rw [projection_injective same]
    | emit | request | guard => cases eq
  | emit label next ih =>
    intro q eq
    cases q with
    | emit label' next' =>
      obtain ⟨rfl, same⟩ := Finite.Normal.emit.inj eq
      rw [ih same]
    | ret | request | guard => cases eq
  | request label l r ihl ihr =>
    intro q eq
    cases q with
    | request label' l' r' =>
      obtain ⟨rfl, hl, hr⟩ := Finite.Normal.request.inj eq
      rw [ihl hl, ihr hr]
    | ret | emit | guard => cases eq
  | guard test low fl fr tl tr ifl ifr itl itr =>
    intro q eq
    cases q with
    | guard test' low' fl' fr' tl' tr' =>
      obtain ⟨rfl, rfl, hfl, hfr, htl, htr⟩ := Finite.Normal.testRequest.inj eq
      rw [ifl hfl, ifr hfr, itl htl, itr htr]
    | ret | emit | request => cases eq

theorem map_outcomes {L : List (Ty Empty)} {n : Nat} (p : CanonicalLive L n) (env : Finite.Assignment n) :
    ((CanonicalLive.payloadDenote.map p.target.packed).of (replyInput n env)).outcomes = p.normal.outcomes env := by
  let := Kleisli.instructions model
  let := modelCoherent
  have sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M :=
    Paper.WithCaseBind.SelectedTerminal.seed_denotes J M (fun _ _ => ⟨rfl, rfl⟩)
  let rep := p.readTree.selected.elaborate.property.packExits
  have modelEq : CanonicalLive.payloadDenote.map p.target.packed =
      Finite.Extensional.Selected.denotation p.readTree :=
    (Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩) sound rep).trans
      (Paper.WithProjectionReturnsAndUnitEta.denoteArrow_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩) rep).symm
  rw [modelEq, ← witnessed_normal p]
  exact p.readTree.packedOutcomes_at_assignment env

theorem eq_of_observations {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n)
    (h : ∀ env, ((CanonicalLive.payloadDenote.map p.target.packed).of (replyInput n env)).outcomes =
      ((CanonicalLive.payloadDenote.map q.target.packed).of (replyInput n env)).outcomes) : p = q := by
  apply normal_injective
  apply Finite.Normal.traceTree_inj
  intro env
  apply Reply.Normal.outcomesWith_injective _ (Reply.Exits.Exit.packed_injective L)
  exact (map_outcomes p env).symm.trans ((h env).trans (map_outcomes q env))

theorem eq_of_packed_eq {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n)
    (h : p.target.packed = q.target.packed) : p = q :=
  eq_of_observations p q (fun env => by rw [h])

theorem readback_eq_iff_packed {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n) :
    p.readback = q.readback ↔ p.target.packed = q.target.packed := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (AcyclicSyntax.selected_readable p.readTree.selected)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (AcyclicSyntax.selected_readable q.readTree.selected)
    change (AcyclicSyntax.read p.readTree.selected.elaborate.val).map Subtype.val =
      (AcyclicSyntax.read q.readTree.selected.elaborate.val).map Subtype.val at h
    rw [ha, hb] at h
    exact congrArg ScopedTarget.packed (Subtype.ext (AcyclicSyntax.read_eq_region a b (Option.some.inj h)))
  · intro h
    exact congrArg CanonicalLive.readback (eq_of_packed_eq p q h)

theorem readback_ne_separated {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n)
    (ne : p.readback ≠ q.readback) :
    ∃ env, ((CanonicalLive.payloadDenote.map p.target.packed).of (replyInput n env)).outcomes ≠
      ((CanonicalLive.payloadDenote.map q.target.packed).of (replyInput n env)).outcomes := by
  classical
  by_contra! agreement
  exact ne (congrArg CanonicalLive.readback (eq_of_observations p q agreement))

private theorem admitted_packed {L : List (Ty Empty)} {n : Nat} {source : SelectedAt (replyContext n) L}
    {p : CanonicalLive L n} (admitted : source.projectionCanonical = p.target) :
    source.packedSource = p.target.packed :=
  source.packed_projectionCanonical.trans (congrArg ScopedTarget.packed admitted)

theorem projection_compare_iff {L : List (Ty Empty)} {n : Nat} (left right : SelectedAt (replyContext n) L)
    (p q : CanonicalLive L n) (hl : left.projectionCanonical = p.target) (hr : right.projectionCanonical = q.target) :
    (left.compareProjectionQuotes right).accepted = true ↔ left.packedSource = right.packedSource := by
  constructor
  · exact (left.compareProjectionQuotes right).sound
  · intro eq
    have live := eq_of_packed_eq p q ((admitted_packed hl).symm.trans (eq.trans (admitted_packed hr)))
    have acceptedEq : (left.compareProjectionQuotes right).accepted =
        (left.projectionCanonical.compare right.projectionCanonical).accepted := by
      unfold SelectedAt.compareProjectionQuotes
      cases left.projectionCanonical.compare right.projectionCanonical <;> rfl
    rw [acceptedEq, hl, hr, live]
    exact (ScopedTarget.compare_accepted_iff q.target q.target (AcyclicSyntax.selected_readable q.readTree.selected)).2 rfl

theorem admitted_readback_ne_separated {L : List (Ty Empty)} {n : Nat} (left right : SelectedAt (replyContext n) L)
    (p q : CanonicalLive L n) (hl : left.projectionCanonical = p.target) (hr : right.projectionCanonical = q.target)
    (ne : p.readback ≠ q.readback) :
    ∃ env, ((CanonicalLive.payloadDenote.map left.packedSource).of (replyInput n env)).outcomes ≠
      ((CanonicalLive.payloadDenote.map right.packedSource).of (replyInput n env)).outcomes := by
  rw [admitted_packed hl, admitted_packed hr]
  exact readback_ne_separated p q ne

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected
