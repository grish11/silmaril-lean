module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Replay

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested

open Kleisli (value)
open Isotope.Semantics (BoundEnv)
open Isotope.LetCase.LocallyNameless (Derivation)
open LambdaSSA (At)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)
private abbrev Packed (L : List Sorts) := value (packedExitType L)

private theorem inner_run {L : List Sorts} (a : InnerNormal L) {n : Nat} {β : BoundCtx Sorts n}
    (ρ : BoundEnv value β) (i : Fin n) (h : β.get i = Bit)
    (outer inner : Bool) (hi : h ▸ ρ i = bit outer)
    (finish : Packed L → Trace (Packed L))
    (onReturn : ∀ x : Exits.Exit L, finish x.packed = pure x.packed) :
    (Kleisli.run model (a.render.operand β i h).2 (ρ.snoc (A := Bit) (bit inner)) >>= finish).outcomes =
      (a.traceTree outer inner).outcomesWith Exits.Exit.packed := by
  simp only [Inner.operand, Kleisli.run, Derivation.denote, pure_bind]
  let γ := (ρ.snoc (A := Bit) (bit inner)).snoc (A := U) PUnit.unit
  have branch (b : ArmNormal L) :
      (Kleisli.run model (b.render.renderPrefix b.emits _ i.succ.succ h).2 γ >>= finish).outcomes =
        (b.traceTree outer).outcomesWith Exits.Exit.packed :=
    b.run_at γ i.succ.succ h outer hi finish (onReturn (b.result outer))
  cases inner
  · exact branch a.whenFalse
  · exact branch a.whenTrue

private theorem prefix_run {L : List Sorts} (req : Bool) (l r : InnerNormal L) (es : List Bool)
    {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) (i : Fin n)
    (h : β.get i = Bit) (outer : Bool) (hi : h ▸ ρ i = bit outer)
    (finish : Packed L → Trace (Packed L))
    (onReturn : ∀ x : Exits.Exit L, finish x.packed = pure x.packed) :
    (Kleisli.run model (requestWithPrefix req false l.render r.render es β i h).2 ρ >>= finish).outcomes =
      (es.foldr Reply.Normal.emit (requestTree req (l.traceTree outer) (r.traceTree outer))).outcomesWith
        Exits.Exit.packed := by
  induction es generalizing n with
  | nil =>
    exact request_run req _ _ ρ finish Exits.Exit.packed _ _
      (fun b => inner_run l ρ i h outer b hi finish onReturn)
      (fun b => inner_run r ρ i h outer b hi finish onReturn)
  | cons e es ih =>
    simp only [requestWithPrefix, Kleisli.run, Derivation.denote, pure_bind, bind_assoc]
    change ((Reply.model.eval (.emit e) PUnit.unit >>= fun u =>
      Kleisli.run model (requestWithPrefix req false l.render r.render es (β.snoc U) i.succ h).2
        (ρ.snoc (A := U) u) >>= finish).outcomes) = _
    rw [Reply.model_emit_bind, ih (ρ.snoc (A := U) PUnit.unit) i.succ h hi]
    rfl

private theorem outer_run {L : List Sorts} (a : OuterNormal L) (ρ : BoundEnv value .nil)
    (b : Bool) (finish : Packed L → Trace (Packed L))
    (onReturn : ∀ x : Exits.Exit L, finish x.packed = pure x.packed) :
    (Kleisli.run model a.render.operand.2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes =
      (a.traceTree b).outcomesWith Exits.Exit.packed := by
  cases a with
  | finish a => exact a.run_at (ρ.snoc (A := Bit) (bit b)) 0 rfl b rfl finish (onReturn (a.result b))
  | request es req l r => exact prefix_run req l r es (ρ.snoc (A := Bit) (bit b)) 0 rfl b rfl finish onReturn

private theorem packed_normal_run (H : Sorts) (L : List Sorts) (p : Normal (H :: L)) :
    programOutcomes H L p.render = p.outcomes := by
  let T := packedExitType (H :: L)
  let ρ := boundEnv value (β := .nil) PUnit.unit
  let body := ((program H L p.render).body.render .base).encode.toLetCase.2
  let finish (x : value T) := Kleisli.run model body (ρ.snoc (A := T) x)
  have ret (x : Exits.Exit (H :: L)) : finish x.packed = pure x.packed :=
    Exits.run_router model (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))
      .base ρ x.1 (LambdaSSA.Semantics.Categorical.labelAt_get (H :: L) x.1) x.2
  exact request_run p.request _ _ ρ finish Exits.Exit.packed _ _
    (fun b => outer_run p.left ρ b finish ret) (fun b => outer_run p.right ρ b finish ret)

theorem programOutcomes_eq_of_sat_proof (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase (equation H L p q))) :
    programOutcomes H L p = programOutcomes H L q :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation H L p q) h PUnit.unit)

theorem programOutcomes_proof (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    programOutcomes H L p = p.normal.outcomes :=
  (programOutcomes_eq_of_sat_proof H L p p.normal.render
    (Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative (derive_render_proof H L p)))).trans
    (packed_normal_run H L p.normal)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested
