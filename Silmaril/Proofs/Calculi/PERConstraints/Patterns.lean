module

public import Silmaril.Calculi.PERConstraints.Patterns.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns.Proofs

open CategoryTheory Silmaril.Formats

variable {base middle next : Congruence.Signature} {Hole : Type}
variable {source target : Signature}

theorem map_id (pattern : Pattern base Hole) : pattern.map (𝟙 base) = pattern := by
  induction pattern with
  | hole _ => rfl
  | node shape children ih =>
    exact congrArg (Pattern.node shape) (funext ih)

theorem map_comp (first : base ⟶ middle) (second : middle ⟶ next) (pattern : Pattern base Hole) :
    pattern.map (first ≫ second) = (pattern.map first).map second := by
  induction pattern with
  | hole _ => rfl
  | node shape children ih =>
    exact congrArg (Pattern.node (second.shapeMap (first.shapeMap shape)))
      (funext fun pos => ih (first.positionMap shape (second.positionMap (first.shapeMap shape) pos)))

theorem plug_map (rename : base ⟶ next) (tuple : Hole → base.carrier.Term) (pattern : Pattern base Hole) :
    (pattern.map rename).plug (rename.term ∘ tuple) = rename.term (pattern.plug tuple) := by
  induction pattern with
  | hole _ => rfl
  | node shape children ih =>
    simp only [Pattern.map, Pattern.plug, rename.makeMap]
    exact congrArg (next.constructors.make (rename.shapeMap shape))
      (funext fun pos => ih (rename.positionMap shape pos))

theorem enabled_map (rename : base ⟶ next) (tuple : Hole → base.carrier.Term) (pattern : Pattern base Hole)
    (enabled : pattern.Enabled tuple) : (pattern.map rename).Enabled (rename.term ∘ tuple) := by
  induction pattern with
  | hole _ => trivial
  | node shape children ih =>
    obtain ⟨root, branches⟩ := enabled
    simpa only [Pattern.map, Pattern.Enabled, plug_map] using
      And.intro (rename.enabledMap shape _ root)
        (fun pos => ih (rename.positionMap shape pos) (branches (rename.positionMap shape pos)))

theorem enabled_of_map (rename : source ⟶ target) (tuple : Hole → source.base.carrier.Term)
    (pattern : Pattern source.base Hole)
    (enabled : (pattern.map rename.constructorMap).Enabled (rename.constructorMap.term ∘ tuple)) :
    pattern.Enabled tuple := by
  induction pattern with
  | hole _ => trivial
  | node shape children ih =>
    simp only [Pattern.map, Pattern.Enabled, plug_map] at enabled
    refine ⟨rename.reflectsEnabled shape _ enabled.1, fun pos => ?_⟩
    obtain ⟨preimage, rfl⟩ := rename.ontoPosition shape pos
    exact ih _ (enabled.2 preimage)

theorem satisfaction (rename : source ⟶ target) (family : Family target) (rule : Rule source) :
    (rule.map rename).Holds family ↔ rule.Holds (reduct rename family) := by
  constructor
  · intro holds left right enabledLeft enabledRight related
    have result := holds (rename.constructorMap.term ∘ left) (rename.constructorMap.term ∘ right)
      (enabled_map rename.constructorMap left rule.pattern enabledLeft)
      (enabled_map rename.constructorMap right rule.pattern enabledRight) related
    simpa only [Rule.map, plug_map, reduct, PER.pull] using result
  · intro holds nextLeft nextRight enabledLeft enabledRight related
    obtain ⟨left, rfl⟩ : ∃ left : Fin rule.arity → source.base.carrier.Term,
        rename.constructorMap.term ∘ left = nextLeft :=
      (Function.Surjective.piMap fun _ : Fin rule.arity => rename.ontoTerm) nextLeft
    obtain ⟨right, rfl⟩ : ∃ right : Fin rule.arity → source.base.carrier.Term,
        rename.constructorMap.term ∘ right = nextRight :=
      (Function.Surjective.piMap fun _ : Fin rule.arity => rename.ontoTerm) nextRight
    have result := holds left right (enabled_of_map rename left rule.pattern enabledLeft)
      (enabled_of_map rename right rule.pattern enabledRight) related
    simpa only [Rule.map, plug_map, reduct, PER.pull] using result

theorem plug_related {model : PER base.carrier.Term} (closed : base.constructors.Closed model)
    (pattern : Pattern base Hole) {left right : Hole → base.carrier.Term}
    (enabledLeft : pattern.Enabled left) (enabledRight : pattern.Enabled right)
    (related : ∀ index, model.rel (left index) (right index)) : model.rel (pattern.plug left) (pattern.plug right) := by
  induction pattern with
  | hole index => exact related index
  | node shape children ih =>
    exact closed shape enabledLeft.1 enabledRight.1 (fun pos => ih pos (enabledLeft.2 pos) (enabledRight.2 pos))

theorem generated_satisfies (rules : Set (Rule source)) (seed : Family source) :
    Satisfies rules (generated rules seed) := by
  intro rule chosen left right enabledLeft enabledRight related model
  exact model.property.2 rule chosen left right enabledLeft enabledRight (fun index => related index model)

end Silmaril.Calculi.PERConstraints.Patterns.Proofs
