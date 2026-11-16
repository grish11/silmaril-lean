module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Logic
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Examples
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Unbounded.Thms

/-! # Finite universe counts for extensional MLTT with W-types

Every inference parameter is uniformly bounded, including both the W family and
its motive. Counts one, two and three have concrete finite-tower consistency
proofs. Institution and logical-system inclusions add available universes through
the existing model restriction maps. This does not assert elimination of a
hierarchy into a single object universe. The unrestricted rule budget recovers
exactly the original W calculus through `Ctx.JEqB.unbounded_iff`.
-/
