module

public import Silmaril.Formats.Dasl.Comparison.Thms
public import Silmaril.Formats.Dasl.Resolve.View.Thms
import Silmaril.Proofs.Formats.Dasl.Comparison.Conservative

public section

namespace Silmaril.Formats.Dasl

variable {Name Next : Type} {source : Store Name} {target : Store Next}

/-- Forgetting a valid lift recovers the value and the chosen shallow view.
A binding store alone does not supply the local naming choices. -/
theorem Named.exists_valid_lift_iff {value : Value} {shallow : Shallow Name} :
    (∃ tree : Named.Valid source, tree.val.erase = value ∧ tree.val.embed.shallow = shallow) ↔
      source.Binding ∧ CanName source value shallow :=
  ⟨fun ⟨tree, erased, view⟩ => ⟨tree.property.1, canName_iff_exists_admitted.mpr
      ⟨tree.val, erased, view, tree.property.2⟩⟩,
   fun ⟨bound, choices⟩ => let ⟨tree, erased, view, admitted⟩ := canName_iff_exists_admitted.mp choices
     ⟨⟨tree, bound, admitted⟩, erased, view⟩⟩

@[simp] theorem Named.Valid.erase_rename (tree : Named.Valid source) (rename : Renaming source target)
    (bound : target.Binding) : (tree.rename rename bound).val.erase = tree.val.erase :=
  Named.erase_rename rename.names tree.val

/-- A root hit is necessary; checking every observed binding supplies the rest of
the evidence for this particular full target. The result is a logical lookup. -/
theorem Reader.fullLookup_eq_some_iff (reader : Reader Name) {root : Name} {tree : Named Name} :
    fullLookup reader.binding root = some tree ↔
      reader.object? root = some tree.embed.shallow ∧ tree.AdmittedBy reader.store :=
  (fullLookup_eq_some reader.binding).trans
    ⟨FullNames.toPartial, fun ⟨hit, admitted⟩ => ⟨_, hit, Named.admitted_iff_expands.mp admitted⟩⟩

/-- Starting with a successful shallow read, the remaining requirements for a
full lookup are reachable closure and absence of infinite dependency descent. -/
theorem Reader.exists_fullLookup_iff_of_hit (reader : Reader Name) {root : Name} {shallow : Shallow Name}
    (hit : reader.object? root = some shallow) :
    (∃ tree, fullLookup reader.binding root = some tree) ↔
      Acc (Depends reader.store) root ∧ ClosedBelow reader.store root :=
  (exists_congr fun _ => fullLookup_eq_some reader.binding).trans <|
    (full_exists_iff reader.binding root).trans ⟨And.right, fun ready => ⟨⟨shallow, hit⟩, ready⟩⟩

/-- A bounded observation that returns this exact full embed is enough; a
successful observation with opaque references is not. -/
theorem Reader.fullLookup_eq_some_iff_observe (reader : Reader Name) {root : Name} {tree : Named Name} :
    fullLookup reader.binding root = some tree ↔
      ∃ fuel, reader.observeRoot? fuel root = some tree.embed :=
  Proofs.Formats.Dasl.fullLookup_eq_some_iff_observe reader

namespace NamedPER

/-- On bundled valid syntax the erasure-pullback reindexing law is just the
commuting erasure square at both endpoints. It makes no injectivity claim. -/
theorem onValid_erasure_rename_iff (base : PER Value) (rename : Renaming source target)
    (bound : target.Binding) (left right : Named.Valid source) :
    (onValid target (base.pull Named.erase)).rel (left.rename rename bound) (right.rename rename bound) ↔
      (onValid source (base.pull Named.erase)).rel left right := by
  change base.rel (left.rename rename bound).val.erase (right.rename rename bound).val.erase ↔
    base.rel left.val.erase right.val.erase
  rw [left.erase_rename, right.erase_rename]

/-- Raw formulation of the same law. Source validity is a premise, not something
inferred from a renamed tree being valid. -/
theorem fromErasure_rename_iff (base : PER Value) (rename : Renaming source target)
    (bound : target.Binding) {left right : Named Name}
    (validLeft : left.Compatible source) (validRight : right.Compatible source) :
    (fromErasure base Next target).rel (left.rename rename.names) (right.rename rename.names) ↔
      (fromErasure base Name source).rel left right :=
  onValid_rel_iff.symm.trans <|
    (onValid_erasure_rename_iff base rename bound ⟨left, validLeft⟩ ⟨right, validRight⟩).trans onValid_rel_iff

end NamedPER
end Silmaril.Formats.Dasl
