module

public import Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Lexical.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Version.Flat

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V K : Type w} {F : Type v}

/-- Reification accepts exactly the readbacks of forward graphs. -/
theorem ofRegion?_eq_some_iff (region : Region V K F) (graph : CFG V K F) :
    ofRegion? region = some graph ↔ graph.toRegion = region :=
  Proofs.SSA.LambdaRTL.CFG.FlatVersion.ofRegion?_eq_some_iff region graph

/-- Reading back and then reifying preserves the entire graph. -/
@[simp] theorem ofRegion?_toRegion (graph : CFG V K F) : ofRegion? graph.toRegion = some graph :=
  (ofRegion?_eq_some_iff _ _).2 rfl

variable [DecidableEq V] [DecidableEq K]

/-- Generate a flat versioned target by running structured versioning and
reifying its result. The erased proof supplies success of reification for
every input graph. -/
def versioned (source : CFG V K F) : CFG (V × Nat) K F :=
  (ofRegion? (Version.versionTop source.toRegion)).get (by
    obtain ⟨target, eq, _⟩ := Proofs.SSA.LambdaRTL.CFG.FlatVersion.version_reifies source
    rw [eq]
    rfl)

/-- The generated target reads back to the exact structured versioner output. -/
theorem versioned_toRegion (source : CFG V K F) :
    source.versioned.toRegion = Version.versionTop source.toRegion :=
  (ofRegion?_eq_some_iff _ _).1 (Option.some_get _).symm

/-- The generated target preserves block labels, their order and multiplicity. -/
theorem versioned_blockLabels (source : CFG V K F) :
    source.versioned.blocks.map Prod.fst = source.blocks.map Prod.fst := by
  obtain ⟨target, eq, labels⟩ := Proofs.SSA.LambdaRTL.CFG.FlatVersion.version_reifies source
  have generated : source.versioned = target := Option.get_of_eq_some _ eq
  exact generated ▸ labels

/-- The target satisfies dominance-scoped SSA in the source's version-zero
input context. -/
theorem versioned_isSSA (source : CFG V K F) :
    source.versioned.toRegion.IsSSA (Version.initCtx source.toRegion) := by
  rw [versioned_toRegion]
  exact Version.versionTop_isSSA _

/-- The generated target preserves the mutable source's exit and payload.
The source inputs come from version zero of the target environment. -/
theorem versioned_runSSA {M : Type w → Type w} {α : Type w}
    [Monad M] [LawfulMonad M] (source : CFG V K F) (model : Model F M α)
    (pairs : model.PairLawful) (input : V × Nat → α) :
    source.versioned.runSSA model input = obs <$> source.run model (fun x => input (x, 0)) :=
  runSSA_eq_obs_of_versioned source _ (versioned_toRegion source) model pairs input

end Silmaril.SSA.LambdaRTL.CFG
