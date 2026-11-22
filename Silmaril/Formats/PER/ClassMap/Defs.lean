module

public import Silmaril.Formats.PER.Fibers.Thms

@[expose] public section

namespace Silmaril.Formats.PER

/-- A partial assignment to a separate class type. Values can be opaque;
the map is not a parent graph, nor does it select any member of a class. -/
abbrev ClassMap (Key Class : Type) := Key → Option Class

namespace ClassMap

variable {Key Class : Type}

/-- Discard unused labels; they need not correspond to any actual class. -/
def Used (lookup : ClassMap Key Class) := {label : Class // ∃ key, lookup key = some label}

def usedLookup (lookup : ClassMap Key Class) (key : Key) : Option (Used lookup) :=
  (lookup key).pbind fun label hit => some ⟨label, key, hit⟩

/-- The intrinsic class assignment does not select a representative. The
classical test guards unsupported keys; no equality test on classes is used. -/
noncomputable def intrinsic (relation : PER Key) : ClassMap Key relation.Quotient :=
  open Classical in fun key => if hit : relation.Dom key then some (_root_.Quotient.mk _ ⟨key, hit⟩) else none

/-- The extensional version returns the set of all members in the class. -/
noncomputable def extensional (relation : PER Key) : ClassMap Key (Set Key) :=
  open Classical in fun key => if relation.Dom key then some (relation.classOf key) else none

/-- Every assigned set is exactly its fiber (hence it contains the key).
This is extra data about set-valued labels, not a law for opaque labels. -/
def Coherent (lookup : ClassMap Key (Set Key)) : Prop :=
  ∀ ⦃key group⦄, lookup key = some group → group = {other | lookup other = some group}

/-- A representative selector must choose a member of every class. -/
def Selects (relation : PER Key) (pick : relation.Quotient → Key) : Prop :=
  ∀ key : {key // relation.Dom key}, relation.rel key.val (pick (_root_.Quotient.mk _ key))

noncomputable def representatives (relation : PER Key) (pick : relation.Quotient → Key) : ClassMap Key Key :=
  fun key => (intrinsic relation key).map pick

noncomputable def canonicalSelector {relation : PER Key} (policy : relation.Canonical) : relation.Quotient → Key :=
  _root_.Quotient.lift (fun key => (policy.normalize key).val)
    (fun left right edge => congrArg Subtype.val ((policy.normalize_eq_iff left right).mpr edge))

end ClassMap
end Silmaril.Formats.PER
