module

public import Silmaril.Semantics.Prolly.Routing.Defs
public import Silmaril.Semantics.Prolly.Thms
import Silmaril.Proofs.Semantics.Prolly.Routing

public section

namespace Silmaril.Semantics.Prolly

variable {Key Payload Child : Type} [LinearOrder Key]

theorem build_routable (policy : Policy Key) (map : Silmaril.Semantics.OrderedMap Key Payload) :
    (build policy map).Routable := Proofs.Semantics.Prolly.Routing.build_routable policy map

/-- With ordered leaf entries and truthful maxima, no skipped sibling contains the query. -/
theorem lookup_children (key : Key) (children : List (Key × Child)) (entries : Child → List (Key × Payload))
    (ordered : (children.flatMap (entries ∘ Prod.snd)).Pairwise fun left right => left.1 < right.1)
    (maxima : ∀ child ∈ children, (entries child.2).getLast?.map Prod.fst = some child.1) :
    (children.flatMap (entries ∘ Prod.snd)).lookup key =
      (selectChild key children).bind (fun child => (entries child.2).lookup key) :=
  Proofs.Semantics.Prolly.Routing.lookup_children key children entries ordered maxima

end Silmaril.Semantics.Prolly
