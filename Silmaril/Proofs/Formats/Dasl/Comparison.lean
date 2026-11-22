module

public import Silmaril.Formats.Dasl.Comparison.Defs
public import Silmaril.Formats.Dasl.Named.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats Silmaril.Formats.Dasl

variable {Name Next : Type} {source : Store Name} {target : Store Next}

theorem valid_map_iff (action : Named Name → Named Next) :
    (∀ tree, tree.Compatible source → (action tree).Compatible target) ↔
      ∃! bundle : Named.Valid source → Named.Valid target, ∀ tree, (bundle tree).val = action tree.val := by
  constructor
  · intro preserves
    refine ⟨(fun tree => ⟨action tree.val, preserves tree.val tree.property⟩), (fun _ => rfl), ?_⟩
    intro other projects
    exact funext fun tree => Subtype.ext (projects tree)
  · rintro ⟨bundle, projects, _⟩ tree valid
    exact projects ⟨tree, valid⟩ ▸ (bundle ⟨tree, valid⟩).property

theorem relabels_of_covered {relates : Link Name → Link Next → Prop} (names : Name → Next) (tree : Named Name)
    (covered : ∀ ⦃link⦄, link ∈ tree.embed.links true → relates link (Link.map names link)) :
    Named.Relabels relates tree (tree.rename names) := by
  induction tree with
  | ref impossible => exact impossible.elim
  | obj _ _ ih => exact .obj (covered (.inl rfl)) (ih (fun {_} hit => covered (.inr hit)))
  | blob _ _ => exact .blob (covered rfl)
  | dict _ _ ih => exact .dict fun key => ih key (fun {_} hit => covered ⟨key, hit⟩)
  | list _ _ ih => exact .list fun index => ih index (fun {_} hit => covered ⟨index, hit⟩)
  | _ => constructor

theorem relabels_eq_rename_of_subgraph {relates : Link Name → Link Next → Prop} (names : Name → Next)
    (within : ∀ ⦃old new⦄, relates old new → Link.map names old = new) {left : Named Name} {right : Named Next}
    (step : Named.Relabels relates left right) : left.rename names = right := by
  induction step with
  | obj hit _ ih =>
    have eq := within hit
    cases eq
    exact congrArg (Tree.obj _) ih
  | blob hit =>
    have eq := within hit
    cases eq
    rfl
  | dict _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

theorem relabels_covered {relates : Link Name → Link Next → Prop} (names : Name → Next)
    (within : ∀ ⦃old new⦄, relates old new → Link.map names old = new) {left : Named Name} {right : Named Next}
    (step : Named.Relabels relates left right) :
    ∀ ⦃link⦄, link ∈ left.embed.links true → relates link (Link.map names link) := by
  induction step with
  | obj present _ ih =>
    rintro link (rfl | hit)
    · exact (within present).symm ▸ present
    · exact ih hit
  | @blob first _ _ present =>
    intro link hit
    change link = .blob first at hit
    exact hit.symm ▸ (within present).symm ▸ present
  | dict _ ih | list _ ih =>
    rintro _ ⟨index, hit⟩
    exact ih index hit
  | _ => intro _ hit; exact hit.elim

theorem relabels_unique {relates : Link Name → Link Next → Prop}
    (functional : ∀ ⦃old first second⦄, relates old first → relates old second → first = second)
    {left : Named Name} {right other : Named Next}
    (step : Named.Relabels relates left right) (rest : Named.Relabels relates left other) : right = other := by
  induction step generalizing other with
  | obj hit _ ih =>
    cases rest with
    | obj next child =>
      have eq := functional hit next
      cases eq
      exact congrArg (Tree.obj _) (ih child)
  | blob hit =>
    cases rest with
    | blob next =>
      have eq := functional hit next
      cases eq
      rfl
  | dict _ ih =>
    cases rest with
    | dict next => exact congrArg (Tree.dict _) (funext fun key => ih key (next key))
  | list _ ih =>
    cases rest with
    | list next => exact congrArg (Tree.list _) (funext fun index => ih index (next index))
  | _ => cases rest; rfl

theorem relabels_erase_eq {relates : Link Name → Link Next → Prop} {left : Named Name} {right : Named Next}
    (step : Named.Relabels relates left right) : left.erase = right.erase := by
  induction step with
  | obj _ _ ih => exact congrArg Value.obj ih
  | dict _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

theorem from_shallow_iff_equality (store : Store Name) {left right : Named Name} :
    (NamedPER.fromShallow Name store).rel left right ↔ (NamedPER.onStore store (PER.equality (Named Name))).rel left right := by
  constructor
  · rintro ⟨validLeft, validRight, same⟩
    change left.embed.shallow = right.embed.shallow at same
    have first := Named.admitted_iff_expands.mp validLeft.2
    have second := Named.admitted_iff_expands.mp validRight.2
    exact ⟨validLeft, validRight, first.unique validLeft.1 (same.symm ▸ second)⟩
  · rintro ⟨validLeft, validRight, same⟩
    exact ⟨validLeft, validRight, congrArg (fun tree : Named Name => tree.embed.shallow) same⟩

end Silmaril.Proofs.Formats.Dasl
