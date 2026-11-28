module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint

/-! # Typed capture movement and local endpoint reduction -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CfgEta (singleCfg)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} {X S D : τ}

/-- Embed the local payload with its captured input. -/
theorem capturePair_typed :
    Tm.BranchValue [S, X] (capturePair : Tm Φ) (Silmaril.product X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.capturePair_typed

variable [HasTy Φ τ]

/-- Variable substitutions that agree on the exact input context give identical typed syntax. -/
theorem region_subst_eq {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) {θ υ : Nat → Tm Φ}
    (h : ∀ ⦃i A⦄, At Γ i A → θ i = υ i) : r.substVars θ = r.substVars υ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.region_subst_eq hr h

/-- At a singleton input, a substitution depends only on the image of slot zero. -/
theorem singleton_subst {P : τ} {L : LCtx τ} {r : Region Φ} (hr : HasType [P] r L)
    {θ υ : Nat → Tm Φ} (h : θ 0 = υ 0) : r.substVars θ = r.substVars υ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.singleton_subst hr h

/-- The carried block has one input and two exits with the original outward type. -/
theorem carryBlock_typed {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    ValueBranches [Silmaril.product X S] (carryBlock p) [Silmaril.product X S, D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.carryBlock_typed hp

/-- Embedding and recovering the capture commutes with a block step by product β. -/
theorem capture_square {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [S, X]
      (p.lsubst carryRepeat)
      ((Region.br 0 capturePair).lsubst (liftLSubstVars (fun _ => carryBlockInCfg p)))
      [Silmaril.product X S, D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.capture_square hp

/-- Move a constructor capture into the state using the existing Paper uniformity rule. -/
theorem move_capture {e p : Region Φ} (he : ValueBranches [X] e [S, D])
    (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [X] (singleCfg e p) (singleCfg (carryEntry e) (carryBlockInCfg p)) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.move_capture he hp

/-- The guarded CFG runs the independent carried loop on its repeat paths. -/
theorem guardedCfg_carried {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [X] (guardedCfg S D e b)
      ((carryEntry (decodeExits e [S, D])).lsubst
        (carriedDispatch (Silmaril.product X S) (carryBlock (decodeExits (Paper.PackedBody.applyPacked b) [S, D])))) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.guardedCfg_carried he hb

/-- For a guarded entry the linked decoder reduces to literal substitution. -/
theorem decodeExits_eq_lsubst {Γ : VCtx τ} {L : LCtx τ} {e : Region Φ}
    (he : ValueBranches Γ e [packedExitType L]) :
    Paper.Eqv Γ (decodeExits e L) (e.lsubst (fun _ => unpackExits L)) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.decodeExits_eq_lsubst he

/-- Reduce the guarded CFG to its local continuation at the packed exit. -/
theorem guardedCfg_exitContinuation {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [X] (guardedCfg S D e b)
      (e.lsubst (fun _ => carriedExitContinuation X S D b)) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.guardedCfg_exitContinuation he hb

/-- Reduce the canonical region to its local continuation at the same packed exit. -/
theorem canonicalRegion_exitContinuation {e step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]) :
    Paper.Eqv [X] (canonicalRegion X S e step)
      (e.lsubst (fun _ => canonicalExitContinuation X S step)) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.canonicalRegion_exitContinuation he hs

/-- A local continuation equation suffices for the exact one-block endpoint comparison. -/
theorem canonicalRegion_eq_guardedCfg_of_exitContinuation {e b step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)])
    (localEq : Paper.Eqv [packedExitType [S, D], X]
      (canonicalExitContinuation X S step) (carriedExitContinuation X S D b) [D]) :
    Paper.Eqv [X] (canonicalRegion X S e step) (guardedCfg S D e b) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint.canonicalRegion_eq_guardedCfg_of_exitContinuation he hb hs localEq

/-- The same local endpoint comparison can be supplied by any typed contextual extension. -/
theorem canonicalRegion_eq_guardedCfg_of_extendedExitContinuation
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {e b step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)])
    (localEq : Paper.Extension.Eqv Seed [packedExitType [S, D], X]
      (canonicalExitContinuation X S step) (carriedExitContinuation X S D b) [D]) :
    Paper.Extension.Eqv Seed [X] (canonicalRegion X S e step) (guardedCfg S D e b) [D] :=
  (Paper.Extension.Eqv.paper (Seed := Seed) (canonicalRegion_exitContinuation he hs)).trans
    ((Paper.Extension.Eqv.lsubstCongr he (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ localEq)).trans
      (.paper (guardedCfg_exitContinuation he hb).symm))

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
