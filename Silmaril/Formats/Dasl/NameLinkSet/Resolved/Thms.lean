module

public import Silmaril.Formats.Dasl.NameLinkSet.Resolved.Defs
import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Formats.Dasl.NameLinkSet.Resolved

public section

namespace Silmaril.Formats.Dasl.NameLinkSet.ResolvedView

open Silmaril.Semantics

variable {Key Name : Type} [LinearOrder Key]
variable {key : Encode.TotalCodec Key (Link Name)} {layout : Layout Key}

theorem shallow_entry (view : ResolvedView key layout) (member : ↥(names layout)) :
    (view.entry member).embed.shallow = .ref (key.encode member.val) :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.shallow_entry view member

theorem shallow_toNamed (view : ResolvedView key layout) :
    view.toNamed.embed.shallow = linkArray.encode (links key layout) :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.shallow_toNamed view

theorem recovers [DecidableEq Name] (view : ResolvedView key layout) :
    (codec key).decode? view.toNamed.embed.shallow = some layout := by
  rw [shallow_toNamed]
  exact (codec key).recovers layout

theorem expands {store : Store Name} {view : ResolvedView key layout} (valid : view.ValidIn store) :
    Expands store view.toNamed.embed.shallow view.toNamed :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.expands valid

theorem contents_eq {rel : Naming.Relation (Link Name) (Named Name)} {view : ResolvedView key layout}
    (valid : view.Valid rel) (bound : Naming.Binding rel) :
    view.contents = NameLinkSet.contents key (fun link value => ∃ target, rel link target ∧ target.erase = value) layout :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.contents_eq valid bound

theorem unique_in {store : Store Name} {left right : ResolvedView key layout} (bound : store.Binding)
    (first : left.ValidIn store) (second : right.ValidIn store) : left.toNamed = right.toNamed := by
  have other := expands second
  rw [right.shallow_toNamed, ← left.shallow_toNamed] at other
  exact (expands first).unique bound other

end Silmaril.Formats.Dasl.NameLinkSet.ResolvedView

namespace Silmaril.Formats.Dasl.NameLinkSet.SortedNamed

variable {Key Name : Type} [LinearOrder Key]
variable {key : Encode.TotalCodec Key (Link Name)}

def ofView {layout : Layout Key} (view : ResolvedView key layout) : SortedNamed key :=
  ⟨view.toNamed, layout, view.shallow_toNamed⟩

theorem valid_ofView {layout : Layout Key} {view : ResolvedView key layout} {store : Store Name}
    (valid : view.ValidIn store) : (ofView view).ValidIn store := ResolvedView.expands valid

variable [DecidableEq Name]

theorem shallow_forget (tree : SortedNamed key) : tree.val.embed.shallow = (codec key).encode tree.forget :=
  Proofs.Formats.Dasl.NameLinkSet.SortedNamed.shallow_forget tree

theorem forget_ofView {layout : Layout Key} (view : ResolvedView key layout) : (ofView view).forget = layout :=
  Proofs.Formats.Dasl.NameLinkSet.SortedNamed.forget_of_shape _ view.shallow_toNamed

theorem lookup_none_iff (tree : SortedNamed key) (query : Key) :
    tree.lookup? query = none ↔ query ∉ names tree.forget :=
  Proofs.Formats.Dasl.NameLinkSet.SortedNamed.lookup_none_iff tree query

theorem lookup_matches (tree : SortedNamed key) (query : Key) {node : Named Name}
    (hit : tree.lookup? query = some node) : node ∈ entries tree.val ∧ node.embed.shallow = .ref (key.encode query) :=
  Proofs.Formats.Dasl.NameLinkSet.SortedNamed.lookup_matches tree query hit

theorem lookup_sound {store : Store Name} {tree : SortedNamed key} (valid : tree.ValidIn store)
    (query : Key) {node : Named Name} (hit : tree.lookup? query = some node) :
    Expands store (.ref (key.encode query)) node :=
  Proofs.Formats.Dasl.NameLinkSet.SortedNamed.lookup_sound valid query hit

def ofExpansion {store : Store Name} {layout : Layout Key} {node : Named Name}
    (expanded : Expands store ((codec key).encode layout) node) : SortedNamed key :=
  ⟨node, layout, expanded.shallow_eq⟩

theorem forget_ofExpansion {store : Store Name} {layout : Layout Key} {node : Named Name}
    (expanded : Expands store ((codec key).encode layout) node) : (ofExpansion expanded).forget = layout :=
  Proofs.Formats.Dasl.NameLinkSet.SortedNamed.forget_of_shape _ expanded.shallow_eq

theorem valid_iff_expands {store : Store Name} (tree : SortedNamed key) :
    tree.ValidIn store ↔ Expands store ((codec key).encode tree.forget) tree.val := by
  unfold ValidIn
  rw [tree.shallow_forget]

/-- Only layouts admitting full expansion correspond to valid named trees.
The inverse to forgetting uses a supplied existence proof, not a resolver algorithm. -/
noncomputable def compatibleEquiv (key : Encode.TotalCodec Key (Link Name)) (store : Store Name)
    (bound : store.Binding) :
    {layout : Layout Key // ∃ node, Expands store ((codec key).encode layout) node} ≃
      {tree : SortedNamed key // tree.ValidIn store} where
  toFun layout :=
    let expanded := layout.property.choose_spec
    ⟨ofExpansion expanded, by
      change Expands store (Named.embed layout.property.choose).shallow layout.property.choose
      rw [expanded.shallow_eq]
      exact expanded⟩
  invFun tree := ⟨tree.val.forget, tree.val.val, (valid_iff_expands tree.val).mp tree.property⟩
  left_inv layout := Subtype.ext (forget_ofExpansion layout.property.choose_spec)
  right_inv tree := Subtype.ext (Subtype.ext (Expands.unique bound
    (Exists.choose_spec ⟨tree.val.val, (valid_iff_expands tree.val).mp tree.property⟩)
    ((valid_iff_expands tree.val).mp tree.property)))

end Silmaril.Formats.Dasl.NameLinkSet.SortedNamed
