module

public import Silmaril.Formats.Dasl.SExp.Thms
public import Silmaril.Formats.SExp.Dasl.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.SExp

variable {Atom Name Ref Item : Type}

/-- Equality of recovered syntax on expanded trees, even if some links are still opaque. -/
def presentationPER (read : Tree Ref Name → Option Item) : PER (Tree Ref Name) :=
  PER.ofDecoder read

/-- The same reader and relation on the fully expanded tree carrier. -/
def namedPER (read : Partial Name → Option Item) : PER (Named Name) :=
  (presentationPER read).pull Named.embed

/-- Root aliases use finite full resolution and successful syntax recovery. -/
def rootPER (store : Store Name) (bound : store.Binding) (read : Partial Name → Option Item) : PER Name where
  rel := Aliases store read
  laws.symm := fun {_ _} related => Silmaril.EncRel.same_symm (E := Names store read) related
  laws.trans := fun {_ _ _} first second =>
    Silmaril.EncRel.Functional.same_trans (E := Names store read) (names_binding bound read) first second

/-- A root for which a finite full view exists. This alone does not imply successful decoding. -/
abbrev FullRoot (store : Store Name) := {root : Name // ∃ tree, FullNames store root tree}

/-- On roots with a full view, this PER can also be computed relationally with `Observes`
when the reader preserves successful recovery under refinement. -/
def observedPER (store : Store Name) (bound : store.Binding) (read : Partial Name → Option Item) :
    PER (FullRoot store) := (rootPER store bound read).pull Subtype.val

/-- Use the very same boxed byte payload in the inline DASL presentation. -/
def Payload.asValue (payload : Payload Atom) : Encode.TotalCodec Atom Value :=
  payload.then (Encode.bytes : Encode.TotalCodec ByteArray Value)

namespace Dotted

/-- Lossless transport to the repository's binary-tree representation. `none` is nil,
not a missing atom or a failed decoding. In particular this accepts improper lists. -/
def readTree (layout : Layout) (payload : Payload Atom) (tree : Tree Ref Name) :
    Option (Tree2 (Option Atom)) := (read layout payload tree).map (SExp2.equivTreeOption Atom)

/-- Transport only the recursively proper part to the inline codec's exact image.
This specification uses the existing proper-subtype equivalence, not a new parser. -/
noncomputable def properAbstract? (layout : Layout) (payload : Payload Atom)
    (atom : Encode.TotalCodec Atom Value) (tree : Tree Ref Name) : Option (SExpDasl.codec atom).Abstract :=
  (read layout payload tree).bind fun datum =>
    if valid : SExp2.IsProper datum then
      some ((SExpDasl.codec atom).intoAbstract ((Formats.SExp.equivProperSubtype Atom).symm ⟨datum, valid⟩))
    else none

end Dotted
end Silmaril.Formats.Dasl.SExp
