module

public import Silmaril.Semantics.IterOps.Defs
import Silmaril.Proofs.Semantics.IterOps.Basic

/-!
# Premonoidal Elgot structure on a family of hom types: theorems

* `kleisli_lawful`: the Kleisli family of a lawful Elgot monad satisfies every
  law of `Ops.Lawful`, with whiskering by the monad's strength.
* `Hom.lawful` (**transfer**): laws transfer backwards along a faithful,
  operation-preserving map. This is the route for concrete typed code. Give
  the concrete operations and a semantic map into a lawful family, prove
  faithfulness and preservation, and the laws follow without separate
  syntactic proofs.
-/

public section

namespace Silmaril.IterOps

universe u w

/-- Kleisli families of lawful Elgot monads are lawful. -/
theorem kleisli_lawful (m : Type u → Type u) [Monad m] [LawfulMonad m] [Silmaril.Elgot.Iterate m]
    [Silmaril.Elgot.LawfulElgotMonad m] : (kleisliOps m).Lawful :=
  Silmaril.Proofs.Semantics.IterOps.kleisli_lawful m

/-- Laws transfer backwards along a faithful, operation-preserving map. -/
theorem Hom.lawful {H H' : Type u → Type u → Type w} {o : Ops H} {o' : Ops H'} (F : Hom o o')
    (h : o'.Lawful) : o.Lawful :=
  Silmaril.Proofs.Semantics.IterOps.transfer F h

end Silmaril.IterOps
