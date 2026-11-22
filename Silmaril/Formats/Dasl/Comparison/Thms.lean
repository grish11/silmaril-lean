module

public import Silmaril.Formats.Dasl.Comparison.Defs
public import Silmaril.Formats.Dasl.Named.Thms
public import Silmaril.Formats.Dasl.PairedShallow.Thms
import Silmaril.Proofs.Formats.Dasl.Comparison

public section

namespace Silmaril.Formats.Dasl

variable {Name Next : Type} {source : Store Name} {target : Store Next}

theorem Named.Compatible.rename {tree : Named Name} (valid : tree.Compatible source)
    (rename : Renaming source target) (bound : target.Binding) : (tree.rename rename.names).Compatible target :=
  rename.preserves_valid bound valid.2

@[simp] theorem Named.Valid.val_rename (tree : Named.Valid source) (rename : Renaming source target)
    (bound : target.Binding) : (tree.rename rename bound).val = tree.val.rename rename.names := rfl

theorem Named.Valid.map_iff (action : Named Name → Named Next) :
    (∀ tree, tree.Compatible source → (action tree).Compatible target) ↔
      ∃! bundle : Named.Valid source → Named.Valid target, ∀ tree, (bundle tree).val = action tree.val :=
  Proofs.Formats.Dasl.valid_map_iff action

theorem Named.compatible_iff_expands {tree : Named Name} :
    tree.Compatible source ↔ source.Binding ∧ Expands source tree.embed.shallow tree :=
  and_congr_right fun _ => Named.admitted_iff_expands

/-- Paired syntax records agreement; the separate expansion witness supplies the target. -/
theorem Expands.rename_via_pair {shallow : Shallow Name} {tree : Named Name}
    (expanded : Expands source shallow tree) (rename : Renaming source target) :
    (PairedShallow.ofConcrete rename.names shallow).AgreesBy rename.names ∧
      Expands target (PairedShallow.ofConcrete rename.names shallow).abstract (tree.rename rename.names) :=
  ⟨PairedShallow.ofConcrete_agrees _ _, by simpa only [PairedShallow.abstract_ofConcrete] using expanded.rename rename⟩

theorem Named.Relabels.subgraph_iff {relates : Link Name → Link Next → Prop} (names : Name → Next)
    (within : ∀ ⦃old new⦄, relates old new → Link.map names old = new) {left : Named Name} {right : Named Next} :
    Named.Relabels relates left right ↔ left.rename names = right ∧
      ∀ ⦃link⦄, link ∈ left.embed.links true → relates link (Link.map names link) :=
  ⟨fun step => ⟨Proofs.Formats.Dasl.relabels_eq_rename_of_subgraph names within step,
      Proofs.Formats.Dasl.relabels_covered names within step⟩,
   fun ⟨eq, covered⟩ => eq ▸ Proofs.Formats.Dasl.relabels_of_covered names left covered⟩

theorem Named.Relabels.graph_iff (names : Name → Next) {left : Named Name} {right : Named Next} :
    Named.Relabels (fun old new => Link.map names old = new) left right ↔ left.rename names = right :=
  (Named.Relabels.subgraph_iff names (fun {_ _} hit => hit)).trans ⟨And.left, fun eq => ⟨eq, fun {_} _ => rfl⟩⟩

theorem Named.Relabels.unique {relates : Link Name → Link Next → Prop}
    (functional : ∀ ⦃old first second⦄, relates old first → relates old second → first = second)
    {left : Named Name} {right other : Named Next}
    (step : Named.Relabels relates left right) (rest : Named.Relabels relates left other) : right = other :=
  Proofs.Formats.Dasl.relabels_unique functional step rest

theorem Named.Relabels.erase_eq {relates : Link Name → Link Next → Prop} {left : Named Name} {right : Named Next}
    (step : Named.Relabels relates left right) : left.erase = right.erase :=
  Proofs.Formats.Dasl.relabels_erase_eq step

theorem Named.Relabels.compatible_of_graph (rename : Renaming source target) (bound : target.Binding)
    {left : Named Name} {right : Named Next} (valid : left.Compatible source)
    (step : Named.Relabels (fun old new => Link.map rename.names old = new) left right) : right.Compatible target :=
  (Named.Relabels.graph_iff _).mp step ▸ valid.rename rename bound

namespace NamedPER

theorem onValid_rel_iff {store : Store Name} {relation : PER (Named Name)} {left right : Named.Valid store} :
    (onValid store relation).rel left right ↔ (onStore store relation).rel left.val right.val :=
  ⟨fun hit => ⟨left.property, right.property, hit⟩, fun hit => hit.2.2⟩

theorem respects_onStore_iff_onValid (rename : Renaming source target) (bound : target.Binding)
    (relation : PER (Named Name)) (other : PER (Named Next)) :
    Respects rename (onStore source relation) (onStore target other) ↔
      ∀ left right : Named.Valid source, (onValid source relation).rel left right →
        (onValid target other).rel (left.rename rename bound) (right.rename rename bound) :=
  ⟨fun law left right related => (law ⟨left.property, right.property, related⟩).2.2,
   fun law {_ _} ⟨left, right, related⟩ => ⟨Named.Compatible.rename left rename bound, Named.Compatible.rename right rename bound,
     law ⟨_, left⟩ ⟨_, right⟩ related⟩⟩

/-- Within a binding store, equal shallow projections uniquely determine compatible
expanded trees. Without validity the same projection can hide different expansions. -/
theorem fromShallow_iff_onStore_equality (store : Store Name) {left right : Named Name} :
    (fromShallow Name store).rel left right ↔ (onStore store (PER.equality (Named Name))).rel left right :=
  Proofs.Formats.Dasl.from_shallow_iff_equality store

theorem onStore_equality_sub_erasure (store : Store Name) :
    (onStore store (PER.equality (Named Name))).Sub (fromErasure (PER.equality Value) Name store) :=
  fun {_ _} ⟨left, right, same⟩ => ⟨left, right, congrArg Named.erase same⟩

end NamedPER
end Silmaril.Formats.Dasl
