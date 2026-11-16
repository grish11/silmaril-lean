module

public import Silmaril.Logic.Temporal.CTLStar.Path.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.PathFormula

/-- Weak next is true when no next position exists. No graph edge is added. -/
def weakNext {S : Signature} (p : PathFormula S) : PathFormula S :=
  .neg (.next (.neg p))

/-- Release is the Boolean dual of strong until, on the existing maximal paths. -/
def release {S : Signature} (p q : PathFormula S) : PathFormula S :=
  .neg (.until (.neg p) (.neg q))

end Silmaril.Logic.Temporal.CTLStar.PathFormula
