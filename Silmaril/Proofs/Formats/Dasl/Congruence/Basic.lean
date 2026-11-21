module
public import Silmaril.Formats.Dasl.Congruence.Defs

public section
namespace Silmaril.Proofs.Formats.Dasl.Congruence
open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Tree
variable {Ref Name : Type} {enabled : Shape Ref Name → Prop}

theorem rules_iff {R : PER (Tree Ref Name)} : Rules enabled R ↔ (constructors enabled).Closed R := by
  constructor
  · intro rules shape left right hl _ rel
    cases shape with
    | leaf leaf => exact rules.leaf leaf hl
    | obj name => exact rules.obj name hl (rel ())
    | dict keys => exact rules.dict keys hl rel
    | list len => exact rules.list len hl rel
  · intro closed
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun leaf h => closed (.leaf leaf) (left := Empty.elim) (right := Empty.elim) h h (fun pos => pos.elim)
    · intro name left right h rel
      exact closed (.obj name) (left := fun _ => left) (right := fun _ => right) h h (fun _ => rel)
    · exact fun keys left right h rel => closed (.dict keys) (left := left) (right := right) h h rel
    · exact fun len left right h rel => closed (.list len) (left := left) (right := right) h h rel

theorem map_closed {NextRef NextName : Type} (refs : Ref → NextRef) (names : Name → NextName)
    {next : Shape NextRef NextName → Prop} {S : PER (Tree NextRef NextName)}
    (guard : ∀ shape, enabled shape → next (shape.map refs names)) (rules : Rules next S) :
    Rules enabled (S.pull (Tree.map refs names)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro leaf h
    have rel := rules.leaf (leaf.map refs names) (guard (.leaf leaf) h)
    cases leaf <;> exact rel
  · exact fun name _ _ h rel => rules.obj (names name) (guard (.obj name) h) rel
  · exact fun keys _ _ h rel => rules.dict keys (guard (.dict keys) h) rel
  · exact fun len _ _ h rel => rules.list len (guard (.list len) h) rel

theorem shallow_closed {enabled : Shape (Link Name) Name → Prop}
    {next : Shape (Link Name) Empty → Prop} {S : PER (Shallow Name)}
    (guard : ∀ shape, enabled shape → next shape.shallow) (rules : Rules next S) :
    Rules enabled (S.pull Partial.shallow) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro leaf h
    have allowed := guard (.leaf leaf) h
    cases leaf <;> exact rules.leaf _ allowed
  · exact fun name _ _ h _ => rules.leaf (.ref (.obj name)) (guard (.obj name) h)
  · exact fun keys _ _ h rel => rules.dict keys (guard (.dict keys) h) rel
  · exact fun len _ _ h rel => rules.list len (guard (.list len) h) rel

theorem equality_closed : (constructors enabled).Closed (PER.equality (Tree Ref Name)) := by
  intro shape left right _ _ related
  exact congrArg (Shape.make shape) (funext related)

theorem total_of_all_enabled {R : PER (Tree Ref Name)} (rules : Rules (fun _ => True) R)
    (tree : Tree Ref Name) : R.Dom tree := by
  induction tree with
  | ref link => exact rules.leaf (.ref link) trivial
  | blob name payload => exact rules.leaf (.blob name payload) trivial
  | i64 bits => exact rules.leaf (.i64 bits) trivial
  | bytes payload => exact rules.leaf (.bytes payload) trivial
  | string value => exact rules.leaf (.string value) trivial
  | bool value => exact rules.leaf (.bool value) trivial
  | null => exact rules.leaf .null trivial
  | obj name _ ih => exact rules.obj name trivial ih
  | dict keys _ ih => exact rules.dict keys trivial ih
  | list len _ ih => exact rules.list len trivial ih

end Silmaril.Proofs.Formats.Dasl.Congruence
