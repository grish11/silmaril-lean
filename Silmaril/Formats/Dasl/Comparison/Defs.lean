module

public import Silmaril.Formats.Dasl.Named.Defs
public import Silmaril.Formats.Dasl.NamedPER.Defs
public import Silmaril.Formats.Dasl.Renaming.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl

variable {Name Next : Type} {source : Store Name} {target : Store Next}

/-- The same recursive action on the existing valid subtype. -/
def Named.Valid.rename (tree : Named.Valid source) (rename : Renaming source target)
    (bound : target.Binding) : Named.Valid target :=
  ⟨tree.val.rename rename.names, rename.preserves_valid bound tree.property.2⟩

/-- A local witness at every corresponding tag and occurrence. This checks syntax,
not whether any of the named targets are admitted by a CAS relation. -/
inductive Named.Relabels (relates : Link Name → Link Next → Prop) : Named Name → Named Next → Prop where
  | obj {first second left right} : relates (.obj first) (.obj second) → Relabels relates left right →
      Relabels relates (.obj first left) (.obj second right)
  | blob {first second bytes} : relates (.blob first) (.blob second) →
      Relabels relates (.blob first bytes) (.blob second bytes)
  | dict {keys : Finset String} {left : ↥keys → Named Name} {right : ↥keys → Named Next} :
      (∀ key, Relabels relates (left key) (right key)) → Relabels relates (.dict keys left) (.dict keys right)
  | list {len : Nat} {left : Fin len → Named Name} {right : Fin len → Named Next} :
      (∀ index, Relabels relates (left index) (right index)) → Relabels relates (.list len left) (.list len right)
  | i64 (bits : UInt64) : Relabels relates (.i64 bits) (.i64 bits)
  | bytes (bytes : ByteArray) : Relabels relates (.bytes bytes) (.bytes bytes)
  | string (text : String) : Relabels relates (.string text) (.string text)
  | bool (value : Bool) : Relabels relates (.bool value) (.bool value)
  | null : Relabels relates .null .null

namespace NamedPER

/-- Restrict the carrier rather than conjoining validity at every PER edge. -/
abbrev onValid (store : Store Name) (relation : PER (Named Name)) : PER (Named.Valid store) :=
  relation.pull Subtype.val

/-- The same related pairs, with endpoint validity stored in different places. -/
def relatedPairsEquiv (store : Store Name) (relation : PER (Named Name)) :
    {pair : Named Name × Named Name // (onStore store relation).rel pair.1 pair.2} ≃
    {pair : Named.Valid store × Named.Valid store // (onValid store relation).rel pair.1 pair.2} where
  toFun := fun ⟨⟨left, right⟩, h⟩ => ⟨(⟨left, h.1⟩, ⟨right, h.2.1⟩), h.2.2⟩
  invFun := fun ⟨⟨left, right⟩, h⟩ => ⟨(left.val, right.val), left.property, right.property, h⟩
  left_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩; rfl

end NamedPER
end Silmaril.Formats.Dasl
