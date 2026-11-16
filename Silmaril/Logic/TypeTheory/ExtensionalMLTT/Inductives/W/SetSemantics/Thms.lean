module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SetSemantics.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Soundness
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.EmbeddingSemantics

/-! # Concrete soundness and preservation of the original model

`Ctx.JEqH.sound` validates every inference of object extensional MLTT with W-types
from valid judgment hypotheses. `Ctx.JEq.consistent` excludes a closed Empty
inhabitant for any supplied hierarchy. `Embedding.judgment_valid` is the semantic
satisfaction condition for the inclusion of original judgments, including the
finite-lookup variant `judgment_validIn`.

The hierarchy's existence remains an explicit model assumption. No infinite
hierarchy, inaccessible-cardinal supply, or finite hierarchy is postulated here.
-/
