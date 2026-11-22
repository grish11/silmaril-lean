module

public import Silmaril.Semantics.Naming.Lift.Defs
import Silmaril.Proofs.Semantics.Naming.Lift

public section

namespace Silmaril.Semantics.Naming.Lift

theorem matches_binding (coordinates : List Coordinate)
    (bound : ∀ coord ∈ coordinates, Binding coord.represents) : Binding (Matches coordinates) :=
  Proofs.Semantics.Naming.Lift.matches_binding coordinates bound

theorem rel_iff_of_match {coordinates : List Coordinate} {inputs : Inputs coordinates} {args : Args coordinates}
    (bound : Binding (Matches coordinates)) (present : Matches coordinates inputs args)
    (predicate : Args coordinates → Prop) : rel predicate inputs ↔ predicate args :=
  ⟨fun ⟨_, matched, holds⟩ => bound matched present ▸ holds, fun holds => ⟨args, present, holds⟩⟩

theorem mem_where_iff {coord : Coordinate} {predicate : coord.Meaning → Prop} {input : coord.Surface} :
    input ∈ where_ coord predicate ↔ ∃ arg, coord.represents input arg ∧ predicate arg :=
  ⟨fun ⟨args, matched, holds⟩ => ⟨args.1, matched.1, holds⟩,
    fun ⟨arg, matched, holds⟩ => ⟨(arg, ()), ⟨matched, trivial⟩, holds⟩⟩

end Silmaril.Semantics.Naming.Lift
