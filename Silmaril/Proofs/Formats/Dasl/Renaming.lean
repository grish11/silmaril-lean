module

public import Silmaril.Formats.Dasl.Renaming.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl

variable {Ref Name Next Last : Type}

theorem tree_map_comp {RefMid RefLast : Type} (refs : Ref → RefMid) (moreRefs : RefMid → RefLast)
    (names : Name → Next) (moreNames : Next → Last) (tree : Tree Ref Name) :
    Tree.map moreRefs moreNames (Tree.map refs names tree) = Tree.map (moreRefs ∘ refs) (moreNames ∘ names) tree := by
  induction tree with
  | obj _ _ ih => exact congrArg (Tree.obj _) ih
  | dict _ _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

theorem tree_map_id (tree : Tree Ref Name) : Tree.map id id tree = tree := by
  induction tree with
  | obj _ _ ih => exact congrArg (Tree.obj _) ih
  | dict _ _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

theorem partial_shallow_rename (names : Name → Next) (tree : Partial Name) :
    (tree.rename names).shallow = Shallow.map names tree.shallow := by
  induction tree with
  | dict _ _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

private theorem store_ext {left right : Store Next} (objects : left.objects = right.objects)
    (blobs : left.blobs = right.blobs) : left = right := by
  cases left; cases right; cases objects; cases blobs; rfl

theorem observed_image (names : Name → Next) (tree : Partial Name) :
    (tree.rename names).bindings = Store.renameImage tree.bindings names := by
  induction tree with
  | obj name child ih =>
    have children := congrArg Semantics.Naming.Stores.objects ih
    have childBlobs := congrArg Semantics.Naming.Stores.blobs ih
    apply store_ext
    · funext next mapped
      change ((next = names name ∧ mapped = (Partial.rename names child).shallow) ∨
        (Partial.rename names child).bindings.objects next mapped) = _
      rw [partial_shallow_rename, children]
      apply propext
      constructor
      · rintro (⟨eq, view⟩ | ⟨old, value, hit, eq, view⟩)
        · exact ⟨name, Partial.shallow child, .inl ⟨rfl, rfl⟩, eq.symm, view.symm⟩
        · exact ⟨old, value, .inr hit, eq, view⟩
      · rintro ⟨old, value, (⟨rfl, rfl⟩ | hit), eq, view⟩
        · exact .inl ⟨eq.symm, view.symm⟩
        · exact .inr ⟨old, value, hit, eq, view⟩
    · exact childBlobs
  | blob name bytes =>
    apply store_ext
    · funext next mapped
      exact propext ⟨False.elim, fun ⟨_, _, impossible, _⟩ => impossible.elim⟩
    · funext next payload
      exact propext ⟨fun ⟨eq, same⟩ => ⟨name, ⟨rfl, same⟩, eq.symm⟩,
        fun ⟨_, ⟨rfl, same⟩, eq⟩ => ⟨eq.symm, same⟩⟩
  | dict keys values ih | list keys values ih =>
    apply store_ext
    · funext next mapped
      apply propext
      constructor
      · rintro ⟨index, hit⟩
        change (Partial.rename names (values index)).bindings.objects next mapped at hit
        rw [ih index] at hit
        obtain ⟨old, value, seen, eq, shallow⟩ := hit
        exact ⟨old, value, ⟨index, seen⟩, eq, shallow⟩
      · rintro ⟨old, value, ⟨index, seen⟩, eq, shallow⟩
        refine ⟨index, ?_⟩
        change (Partial.rename names (values index)).bindings.objects next mapped
        rw [ih index]
        exact ⟨old, value, seen, eq, shallow⟩
    · funext next bytes
      apply propext
      constructor
      · rintro ⟨index, hit⟩
        change (Partial.rename names (values index)).bindings.blobs next bytes at hit
        rw [ih index] at hit
        obtain ⟨old, seen, eq⟩ := hit
        exact ⟨old, ⟨index, seen⟩, eq⟩
      · rintro ⟨old, ⟨index, seen⟩, eq⟩
        refine ⟨index, ?_⟩
        change (Partial.rename names (values index)).bindings.blobs next bytes
        rw [ih index]
        exact ⟨old, seen, eq⟩
  | _ =>
    apply store_ext
    · funext next mapped
      exact propext ⟨False.elim, fun ⟨_, _, impossible, _⟩ => impossible.elim⟩
    · funext next bytes
      exact propext ⟨False.elim, fun ⟨_, impossible, _⟩ => impossible.elim⟩

theorem extends_rename (names : Name → Next) {left right : Partial Name} (step : Extends left right) :
    Extends (left.rename names) (right.rename names) := by
  induction step with
  | same tree => exact .same (tree.rename names)
  | openObj name target => exact .openObj (names name) (Partial.rename names target)
  | openBlob name bytes => exact .openBlob (names name) bytes
  | obj _ _ ih => exact .obj _ ih
  | dict _ ih => exact .dict ih
  | list _ ih => exact .list ih

theorem expands_rename {source : Store Name} {target : Store Next} (rename : Renaming source target)
    {shallow : Shallow Name} {tree : Named Name} (expanded : Expands source shallow tree) :
    Expands target (Shallow.map rename.names shallow) (tree.rename rename.names) := by
  induction expanded with
  | obj hit _ ih => exact .obj (rename.objects hit) ih
  | blob hit => exact .blob (rename.blobs hit)
  | list _ ih => exact .list ih
  | dict _ ih => exact .dict ih
  | _ => constructor

end Silmaril.Proofs.Formats.Dasl
