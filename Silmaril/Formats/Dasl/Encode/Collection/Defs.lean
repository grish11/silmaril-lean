module

public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Semantics.OrderedMap.Finite.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics

variable {Source Layout Target Key Item Name Ref : Type}

/-- Reuse a layout codec through a lawful change of source representation. -/
def TotalCodec.viaEquiv (layout : Source ≃ Layout) (codec : TotalCodec Layout Target) :
    TotalCodec Source Target where
  encode value := codec.encode (layout value)
  decode? repr := (codec.decode? repr).map layout.symm
  recovers value := by simp [codec.recovers]

def PartialCodec.viaEquiv (layout : Source ≃ Layout) (codec : PartialCodec Layout Target) :
    PartialCodec Source Target where
  encode? value := codec.encode? (layout value)
  decode? repr := (codec.decode? repr).map layout.symm
  recovers _ _ hit := by rw [codec.recovers hit]; simp

/-- A finite map layout, with independent key, value and entry representations.
`TotalCodec` implies injectivity of emitted key trees; the underlying decoder
still rejects repeated *decoded* keys, including aliases. -/
abbrev finiteMap [LinearOrder Key]
    (entry : TotalCodec (Tree Ref Name × Tree Ref Name) (Tree Ref Name))
    (key : TotalCodec Key (Tree Ref Name)) (item : TotalCodec Item (Tree Ref Name)) :
    TotalCodec (OrderedMap Key Item) (Tree Ref Name) := mapWith entry key item

/-- A canonical ascending array for a finite set, with an independent element codec. -/
def finiteSet [LinearOrder Key] (key : TotalCodec Key (Tree Ref Name)) :
    TotalCodec (Finset Key) (Tree Ref Name) := (setOf key).viaEquiv OrderedSet.finsetEquiv

/-- A representation can be accepted by the decoder without being emitted by
the encoder. This observation forgets layout and observes the decoded lookup. -/
def RepresentsMap [LinearOrder Key] (codec : TotalCodec (OrderedMap Key Item) Target)
    (repr : Target) (lookup : Key → Option Item) : Prop :=
  ∃ map, codec.decode? repr = some map ∧ map.lookup? = lookup

def RepresentsSet [DecidableEq Key] (codec : TotalCodec (Finset Key) Target)
    (repr : Target) (members : Set Key) : Prop :=
  ∃ keys, codec.decode? repr = some keys ∧ (keys : Set Key) = members

end Silmaril.Formats.Dasl.Encode
