module

public import Silmaril.Formats.Dasl.NameLinkSet.Resolved.Defs
import all Silmaril.Formats.Dasl.Encode.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.NameLinkSet.Resolved

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet Silmaril.Semantics

variable {Key Name : Type} [LinearOrder Key]
variable {key : Encode.TotalCodec Key (Link Name)} {layout : Layout Key}

theorem shallow_entry (view : ResolvedView key layout) (member : ↥(names layout)) :
    (view.entry member).embed.shallow = .ref (key.encode member.val) := by
  unfold ResolvedView.entry
  generalize view member = target
  generalize key.encode member.val = link at target ⊢
  cases link <;> rfl

private theorem list_congr {left right : Nat} (same : left = right)
    {source : Fin left → Shallow Name} {target : Fin right → Shallow Name}
    (pointwise : ∀ position, source position = target (Fin.cast same position)) :
    Tree.list left source = Tree.list right target := by
  subst right
  exact congrArg (Tree.list left) (funext pointwise)

theorem shallow_toNamed (view : ResolvedView key layout) :
    view.toNamed.embed.shallow = linkArray.encode (links key layout) := by
  simp only [ResolvedView.toNamed, Named.embed, Tree.map, Partial.shallow, linkArray,
    Encode.listOf, Encode.TotalCodec.then, Encode.TotalCodec.listCodec, Encode.TotalCodec.listEncode,
    Encode.list, links]
  apply list_congr (by simp)
  intro position
  change (view.entry (ResolvedView.memberAt layout position)).embed.shallow = _
  rw [shallow_entry]
  simp [ResolvedView.memberAt, Encode.link, List.get_eq_getElem]
  rfl

theorem expands {store : Store Name} {view : ResolvedView key layout} (valid : view.ValidIn store) :
    Expands store view.toNamed.embed.shallow view.toNamed := by
  change Expands store (.list layout.keys.length fun position =>
    (view.entry (ResolvedView.memberAt layout position)).embed.shallow) view.toNamed
  refine .list fun position => ?_
  rw [shallow_entry]
  exact valid _

theorem contents_eq {rel : Naming.Relation (Link Name) (Named Name)} {view : ResolvedView key layout}
    (valid : view.Valid rel) (bound : Naming.Binding rel) :
    view.contents = NameLinkSet.contents key (fun link value => ∃ target, rel link target ∧ target.erase = value) layout := by
  ext value
  change (∃ member, (view.entry member).erase = value) ↔
    ∃ name ∈ names layout, ∃ target, rel (key.encode name) target ∧ target.erase = value
  constructor
  · rintro ⟨member, erased⟩
    exact ⟨member.val, member.property, view.entry member, valid member, erased⟩
  · rintro ⟨name, member, target, resolves, erased⟩
    exact ⟨⟨name, member⟩, (bound (valid ⟨name, member⟩) resolves) ▸ erased⟩

end Silmaril.Proofs.Formats.Dasl.NameLinkSet.Resolved

namespace Silmaril.Proofs.Formats.Dasl.NameLinkSet.SortedNamed

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet Silmaril.Semantics
open Silmaril.Formats.Dasl.NameLinkSet.SortedNamed

variable {Key Name : Type} [LinearOrder Key] [DecidableEq Name]
variable {key : Encode.TotalCodec Key (Link Name)}

theorem forget_of_shape (tree : SortedNamed key) {layout : Layout Key}
    (shape : tree.val.embed.shallow = (codec key).encode layout) : tree.forget = layout := by
  unfold forget
  exact Option.get_of_eq_some _ (shape ▸ (codec key).recovers layout)

theorem shallow_forget (tree : SortedNamed key) :
    tree.val.embed.shallow = (codec key).encode tree.forget := by
  obtain ⟨layout, shape⟩ := tree.property
  rw [forget_of_shape tree shape]
  exact shape

omit [DecidableEq Name] in
private theorem decode_entry (node : Named Name) : Encode.link.decode? node.embed.shallow = entryLink? node := by
  cases node with
  | ref impossible => exact impossible.elim
  | obj _ _ | blob _ _ | dict _ _ | list _ _ | i64 _ | bytes _ | string _ | bool _ | null => rfl

omit [DecidableEq Name] in
private theorem entries_decode {tree : Named Name} {links : List (Link Name)}
    (hit : linkArray.decode? tree.embed.shallow = some links) :
    (entries tree).mapM entryLink? = some links := by
  cases tree with
  | ref impossible => exact impossible.elim
  | list _ children =>
    change ((List.ofFn ((fun node : Named Name => node.embed.shallow) ∘ children)).mapM Encode.link.decode?) =
      some links at hit
    rw [← List.map_ofFn, List.mapM_map] at hit
    simpa [entries, Function.comp_def, decode_entry] using hit
  | obj _ _ | blob _ _ | dict _ _ | i64 _ | bytes _ | string _ | bool _ | null => cases hit

omit [DecidableEq Name] in
private theorem mem_decoded {nodes : List (Named Name)} {actual : List (Link Name)}
    (hit : nodes.mapM entryLink? = some actual) (link : Link Name) :
    link ∈ actual ↔ ∃ node ∈ nodes, entryLink? node = some link := by
  induction nodes generalizing actual with
  | nil => simp at hit; subst actual; simp
  | cons node tail ih =>
    simp only [List.mapM_cons] at hit
    cases parsed : entryLink? node with
    | none => simp [parsed] at hit
    | some head =>
      cases rest : tail.mapM entryLink? with
      | none => simp [parsed, rest] at hit
      | some links =>
        simp [parsed, rest] at hit
        subst actual
        simp [ih rest, parsed, eq_comm, or_and_right, exists_or]

theorem lookup_none_iff (tree : SortedNamed key) (query : Key) :
    tree.lookup? query = none ↔ query ∉ names tree.forget := by
  have decoded : (entries tree.val).mapM entryLink? = some (links key tree.forget) :=
    entries_decode (by rw [shallow_forget]; exact linkArray.recovers _)
  have present : key.encode query ∈ links key tree.forget ↔ query ∈ names tree.forget := by
    simp [links, List.mem_map, names, key.injective.eq_iff]
  rw [lookup?, List.find?_eq_none, ← present, mem_decoded decoded]
  simp

theorem lookup_matches (tree : SortedNamed key) (query : Key) {node : Named Name}
    (hit : tree.lookup? query = some node) : node ∈ entries tree.val ∧ node.embed.shallow = .ref (key.encode query) := by
  unfold lookup? at hit
  have selected := List.find?_some hit
  have found : entryLink? node = some (key.encode query) := of_decide_eq_true selected
  refine ⟨List.mem_of_find?_eq_some hit, ?_⟩
  cases node <;> simp_all [entryLink?, Named.embed, Tree.map, Partial.shallow]

omit [DecidableEq Name] in
private theorem expands_entry {store : Store Name} {tree node : Named Name}
    (valid : Expands store tree.embed.shallow tree) (member : node ∈ entries tree) :
    Expands store node.embed.shallow node := by
  cases tree <;> simp [entries, List.mem_ofFn] at member
  case list len children =>
    obtain ⟨position, rfl⟩ := member
    cases valid with
    | list each => exact each position

theorem lookup_sound {store : Store Name} {tree : SortedNamed key} (valid : tree.ValidIn store)
    (query : Key) {node : Named Name} (hit : tree.lookup? query = some node) :
    Expands store (.ref (key.encode query)) node := by
  obtain ⟨member, shape⟩ := lookup_matches tree query hit
  exact shape ▸ expands_entry valid member

end Silmaril.Proofs.Formats.Dasl.NameLinkSet.SortedNamed
