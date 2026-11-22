module

public import Silmaril.Formats.Dasl.SExp.Bridge.Defs
import Silmaril.Proofs.Formats.Dasl.SExp.Bridge

public section

namespace Silmaril.Formats.Dasl.SExp

variable {Atom Name Ref Item Target : Type} {store : Store Name}

theorem presentation_dom (read : Tree Ref Name → Option Item) (tree : Tree Ref Name) :
    (presentationPER read).Dom tree ↔ ∃ item, read tree = some item := PER.ofDecoder_dom read tree

theorem named_dom (read : Partial Name → Option Item) (tree : Named Name) :
    (namedPER read).Dom tree ↔ ∃ item, read tree.embed = some item := presentation_dom read tree.embed

theorem root_dom (bound : store.Binding) (read : Partial Name → Option Item) (root : Name) :
    (rootPER store bound read).Dom root ↔ ∃ item, Names store read root item :=
  ⟨fun ⟨item, hit, _⟩ => ⟨item, hit⟩, fun ⟨item, hit⟩ => ⟨item, hit, hit⟩⟩

theorem observed_rel (bound : store.Binding) (read : Partial Name → Option Item)
    (mono : ∀ ⦃low high item⦄, Extends low high → read low = some item → read high = some item)
    (left right : FullRoot store) : (observedPER store bound read).rel left right ↔
    ∃ item, Observes store read left.val item ∧ Observes store read right.val item :=
  Proofs.Formats.Dasl.SExp.Bridge.observed_rel bound read mono left right

theorem presentation_rel_normalize (read : Tree Ref Name → Option Item)
    (codec : Encode.TotalCodec Item Target) (left right : Tree Ref Name) :
    (presentationPER read).rel left right ↔ ∃ normal,
      normalize read codec.encode left = some normal ∧ normalize read codec.encode right = some normal :=
  Proofs.Formats.Dasl.SExp.Bridge.presentation_rel_normalize read codec left right

theorem root_rel_normalize (bound : store.Binding) (read : Partial Name → Option Item)
    (codec : Encode.TotalCodec Item Target) {left right : Name} {leftTree rightTree : Named Name}
    (leftFull : FullNames store left leftTree) (rightFull : FullNames store right rightTree) :
    (rootPER store bound read).rel left right ↔ ∃ normal,
      normalize read codec.encode leftTree.embed = some normal ∧
      normalize read codec.encode rightTree.embed = some normal :=
  aliases_iff_normalize bound read codec leftFull rightFull

theorem Proper.inline_write (payload : Payload Atom) (item : Formats.SExp Atom) :
    Proper.write (Ref := Empty) (Name := Unit) payload inlineAll item = SExpDasl.encode payload.asValue item :=
  Proofs.Formats.Dasl.SExp.Bridge.inline_write_at payload item []

theorem Proper.rivest_inline (item : Formats.SExp Bytes) :
    Proper.write (Ref := Empty) (Name := Unit) Payload.bytes inlineAll (item.map Bytes.data) =
      SExpDasl.rivest.encode item := Proofs.Formats.Dasl.SExp.Bridge.rivest_inline item

theorem Proper.abstract_recover (payload : Payload Atom) (atom : Encode.TotalCodec Atom Value)
    (tree : Tree Ref Name) :
    ((SExpDasl.codec atom).parseAbstract? (Proper.read payload) tree).bind
      (SExpDasl.codec atom).fromAbstract? = Proper.read payload tree :=
  (SExpDasl.codec atom).parseAbstract_recover (Proper.read payload) tree

theorem Proper.abstract_write (payload : Payload Atom) (atom : Encode.TotalCodec Atom Value)
    (put : Placement (Formats.SExp Atom) Name) (item : Formats.SExp Atom) :
    (SExpDasl.codec atom).parseAbstract? (Proper.read payload) (Proper.write (Ref := Ref) payload put item) =
      some ((SExpDasl.codec atom).intoAbstract item) := by
  simp [Encode.TotalCodec.parseAbstract?, Proper.read_write]

theorem Proper.abstract_per (payload : Payload Atom) (atom : Encode.TotalCodec Atom Value) :
    PER.ofDecoder ((SExpDasl.codec atom).parseAbstract? (Proper.read (Ref := Ref) (Name := Name) payload)) =
      presentationPER (Proper.read payload) :=
  (SExpDasl.codec atom).parseAbstract_per (Proper.read payload)

theorem Dotted.tree_recover (layout : Dotted.Layout) (payload : Payload Atom) (tree : Tree Ref Name) :
    (Dotted.readTree layout payload tree).map (SExp2.equivTreeOption Atom).symm = Dotted.read layout payload tree := by
  simp [Dotted.readTree, Option.map_map, Function.comp_def]

theorem Dotted.tree_per (layout : Dotted.Layout) (payload : Payload Atom) :
    PER.ofDecoder (Dotted.readTree (Ref := Ref) (Name := Name) layout payload) =
      presentationPER (Dotted.read layout payload) :=
  PER.ext fun left right => (presentation_rel_normalize (Dotted.read layout payload)
    ⟨SExp2.equivTreeOption Atom, fun value => some ((SExp2.equivTreeOption Atom).symm value),
      fun item => congrArg some ((SExp2.equivTreeOption Atom).symm_apply_apply item)⟩ left right).symm

theorem Dotted.proper_abstract_hit (layout : Dotted.Layout) (payload : Payload Atom)
    (atom : Encode.TotalCodec Atom Value) (tree : Tree Ref Name) (item : Formats.SExp Atom) :
    Dotted.properAbstract? layout payload atom tree = some ((SExpDasl.codec atom).intoAbstract item) ↔
      Dotted.read layout payload tree = some item.toSExp2 :=
  Proofs.Formats.Dasl.SExp.Bridge.dotted_proper_hit layout payload atom tree item

theorem Dotted.proper_abstract_rejects_improper (layout : Dotted.Layout) (payload : Payload Atom)
    (atom : Encode.TotalCodec Atom Value) {tree : Tree Ref Name} {datum : SExp2 Atom}
    (hit : Dotted.read layout payload tree = some datum) (improper : ¬ SExp2.IsProper datum) :
    Dotted.properAbstract? layout payload atom tree = none := by
  simp [Dotted.properAbstract?, hit, improper]

end Silmaril.Formats.Dasl.SExp
