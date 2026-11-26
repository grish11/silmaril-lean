module

public import Silmaril.Logic.SAT.Institution.Ordinary.Defs

@[expose] public section

namespace Silmaril.Logic.SAT.Institution

universe u v
variable {A : Type u} {B : Type v}

open Set

/-- Target completions reduce into the source completion family. -/
theorem completion_reduct_image_subset (f : A → B) (v : PartialValuation B) :
    reduct f '' {t | Completes v t} ⊆ {s | Completes (reduct f v) s} :=
  fun {_} ⟨_, ht, h⟩ => h ▸ completes_reduct f ht

/-- Coverage makes the reduct image the entire source completion family. -/
theorem completion_reduct_image_eq_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) :
    reduct f '' {t | Completes v t} = {s | Completes (reduct f v) s} :=
  Subset.antisymm (completion_reduct_image_subset f v) (fun {s} hs => covers s hs)

end Silmaril.Logic.SAT.Institution
