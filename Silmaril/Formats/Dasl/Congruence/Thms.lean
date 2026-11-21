module
public import Silmaril.Formats.Dasl.Congruence.Defs
import Silmaril.Proofs.Formats.Dasl.Congruence.Basic

public section
namespace Silmaril.Formats.Dasl.Tree
variable {Ref Name : Type} {enabled : Shape Ref Name → Prop} {R : PER (Tree Ref Name)}

theorem rules_iff_closed : Rules enabled R ↔ (constructors enabled).Closed R :=
  Proofs.Formats.Dasl.Congruence.rules_iff

theorem generated_rules (R : PER (Tree Ref Name)) : Rules enabled ((constructors enabled).generated R) :=
  rules_iff_closed.mpr ((constructors enabled).generated_closed R)

theorem total_of_all_enabled (rules : Rules (fun _ => True) R) (tree : Tree Ref Name) : R.Dom tree :=
  Proofs.Formats.Dasl.Congruence.total_of_all_enabled rules tree

theorem generated_le_iff {S : PER (Tree Ref Name)} (rules : Rules enabled S) :
    (constructors enabled).generated R ≤ S ↔ R ≤ S :=
  ⟨fun h => ((constructors enabled).le_generated R).trans h,
    fun h => (constructors enabled).generated_le h (rules_iff_closed.mp rules)⟩

/-- Constructors themselves never generate unequal terms from a diagonal seed. -/
theorem generated_eq_only (diagonal : R ≤ PER.equality (Tree Ref Name)) :
    (constructors enabled).generated R ≤ PER.equality (Tree Ref Name) :=
  (constructors enabled).generated_le diagonal Proofs.Formats.Dasl.Congruence.equality_closed

/-- Forward transport only, including erasure and the full/shallow inclusions. This does
not add a names-equal axiom in the source when the target map is noninjective. -/
theorem map_generated {NextRef NextName : Type} (refs : Ref → NextRef) (names : Name → NextName)
    {next : Shape NextRef NextName → Prop} {S : PER (Tree NextRef NextName)}
    (guard : ∀ shape, enabled shape → next (shape.map refs names)) (seed : R ≤ S.pull (Tree.map refs names)) :
    (constructors enabled).generated R ≤ ((constructors next).generated S).pull (Tree.map refs names) :=
  (constructors enabled).map_generated _ _ seed
    (rules_iff_closed.mp (Proofs.Formats.Dasl.Congruence.map_closed refs names guard (generated_rules S)))

theorem shallow_generated {enabled : Shape (Link Name) Name → Prop} {R : PER (Partial Name)}
    {next : Shape (Link Name) Empty → Prop} {S : PER (Shallow Name)}
    (guard : ∀ shape, enabled shape → next shape.shallow) (seed : R ≤ S.pull Partial.shallow) :
    (constructors enabled).generated R ≤ ((constructors next).generated S).pull Partial.shallow :=
  (constructors enabled).map_generated _ _ seed
    (rules_iff_closed.mp (Proofs.Formats.Dasl.Congruence.shallow_closed guard (generated_rules S)))

end Silmaril.Formats.Dasl.Tree
