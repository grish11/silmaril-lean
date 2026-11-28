module

public import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Defs
import Silmaril.Proofs.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Schedule
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Proofs

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (i1)
open LambdaSSA.Acyclic.Theta
open LambdaSSA.Acyclic.Theta.Translation
open LambdaSSA.OrderedTheta (point)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.Part (Runs)
open NestedTheta.Partial (observe)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ Φ ε σ : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{0,0} τ] [InstructionModel Φ τ ε (StateT σ Part)]
variable {A : τ} {w : Width} {g : Graph Φ ε A}
variable (f : Admission g)

private theorem candidate_observe (c : PureTheta.Prefix.Candidate Φ ε A A A A A A (Rows A))
    (leaf : Leaf Φ A) (suffix : c.tail = leaf.syntax.graph) (x : TyDen A) (initial : σ) :
    observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) c.emit (point x initial) =
      ((iter (c.loop.step (σ := σ)) x).run initial).bind (fun (mid, token) =>
        Part.map (ExplicitRuntime.exitTuple (A := A))
          ((iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) leaf.loop) mid).run token)) := by
  rw [PureTheta.Prefix.Candidate.emit, PureTheta.Prefix.linkRecovered,
    MixedContinuation.linkRecovered_observe, PureTheta.Prefix.producer, PureTheta.Prefix.enterGraph_observe,
    c.loop.step_observe, Part.bind_eq_bind, Part.bind_map, Part.bind_map]
  congr 1
  funext p
  obtain ⟨mid, token⟩ := p
  change Sequential.Flat.Serial.observe (ε := ε) c.tail mid token = _
  rw [suffix]
  exact (Sequential.Flat.Serial.loop_observe (ε := ε) leaf.loop mid token).trans
    (ExplicitRuntime.graph_observe (ε := ε) leaf.loop mid token)

theorem observe_splice (x : TyDen A) (initial : σ) :
    observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point x initial) =
      ((iter (f.recovered.shape.loop.step (σ := σ)) x).run initial).bind (fun (mid, token) =>
        Part.map (ExplicitRuntime.exitTuple (A := A))
          ((iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) f.leaf.loop) mid).run token)) :=
  (congrArg (fun graph => observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ))
    graph (point x initial)) f.recovered.wiring.symm).trans
    (candidate_observe f.recovered.shape f.leaf f.suffix x initial)

theorem returns_iff (codec : TyDen A ≃ BitVec w.val) (input : TyDen A)
    (initial : σ) (label : LabelDen [A,A]) (final : σ) :
    observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) =
      Part.some (ExplicitRuntime.exitTuple (A := A) (label, final)) ↔
    ∃ fuel, ((lower w f).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
      Part.some (some (exitPacket codec label), final) := by
  refine Iff.trans ?_ (cfg_iff codec f.recovered.shape.loop f.recovered.shape.pureFirst f.leaf
    input initial label final).symm
  rw [observe_splice f, Part.eq_some_iff, Part.mem_bind_iff]
  refine exists_congr fun mid => and_congr ?_ ?_
  · rw [Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  · rcases mid with ⟨mid, token⟩
    rw [Part.mem_map_iff, Elgot.StateT.run_iter]
    constructor
    · rintro ⟨found, ran, same⟩
      have eq : found = (label, final) := ExplicitRuntime.exitTuple_injective same
      exact (Elgot.Part.mem_iter_iff _ _ _).mp (eq ▸ ran)
    · intro ran
      exact ⟨(label, final), (Elgot.Part.mem_iter_iff _ _ _).mpr ran, rfl⟩

private theorem exitPacket_surjective (codec : TyDen A ≃ BitVec w.val) :
    Function.Surjective (exitPacket codec) := by
  intro output
  cases output with
  | cons tag tail =>
    cases tail with
    | cons word tail =>
      cases tail
      rcases BitVec.eq_zero_or_eq_one tag with h | h
      · exact ⟨.inl (codec.symm word), by simp [exitPacket, packet, h]⟩
      · exact ⟨.inr (.inl (codec.symm word)), by simp [exitPacket, packet, h]⟩

theorem no_return_iff (codec : TyDen A ≃ BitVec w.val) (input : TyDen A) (initial : σ) :
    observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) = Part.none ↔
    ∀ (output : Env [i1,w]) (final : σ), ¬ ∃ fuel,
      ((lower w f).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
        Part.some (some output, final) := by
  constructor
  · intro undefined output final ran
    obtain ⟨label, rfl⟩ := exitPacket_surjective codec output
    have returned := (returns_iff f codec input initial label final).mpr ran
    rw [undefined] at returned
    exact Part.none_ne_some _ returned
  · intro noReturn
    apply Part.eq_none_iff.mpr
    intro output observed
    rw [observe_splice f, Part.mem_bind_iff] at observed
    obtain ⟨⟨mid, token⟩, headRan, observed⟩ := observed
    have exit := observed
    rw [Part.mem_map_iff] at exit
    obtain ⟨⟨label, final⟩, _, rfl⟩ := exit
    exact noReturn _ _ ((returns_iff f codec input initial label final).mp (Part.eq_some_iff.mpr
      (by
        rw [observe_splice f, Part.mem_bind_iff]
        exact ⟨(mid, token), headRan, observed⟩)))

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Proofs
