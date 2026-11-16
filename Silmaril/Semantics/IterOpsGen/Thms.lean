module

public import Silmaril.Semantics.IterOpsGen.Defs
public import Silmaril.Semantics.IterOps.Thms

/-!
# The generated sub-structure: theorems

* `genOps_lawful`: the sub-structure generated in a lawful `Ops` is lawful, by transfer along
  the inclusion (`IterOps.Hom.lawful`).
* `genOps_kleisli_lawful`: in particular in the Kleisli operations of a lawful Elgot monad
  (`kleisli_lawful`).
* `gen_iff_exists`: a hom is generated exactly when it is the image of a hom of the generated
  sub-structure under the inclusion.
-/

public section

namespace Silmaril.IterOps

universe u w

variable {H : Type u → Type u → Type w}

/-- **The generated sub-structure of a lawful structure is lawful.** -/
theorem genOps_lawful {o : Ops H} (G : ∀ {A B : Type u}, H A B → Prop) (h : o.Lawful) :
    (genOps o G).Lawful :=
  (genIncl o G).lawful h

/-- The generated sub-structure of the Kleisli operations of a lawful Elgot monad is lawful. -/
theorem genOps_kleisli_lawful (m : Type u → Type u) [Monad m] [LawfulMonad m]
    [Silmaril.Elgot.Iterate m] [Silmaril.Elgot.LawfulElgotMonad m]
    (G : ∀ {A B : Type u}, (A → m B) → Prop) : (genOps (kleisliOps m) G).Lawful :=
  genOps_lawful G (kleisli_lawful m)

/-- Generated homs are the image of the inclusion. -/
theorem gen_iff_exists {o : Ops H} {G : ∀ {A B : Type u}, H A B → Prop} {A B : Type u}
    (f : H A B) : Gen o G f ↔ ∃ g : GHom o G A B, (genIncl o G).map g = f :=
  ⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨g, hg⟩ => hg ▸ g.2⟩

end Silmaril.IterOps
