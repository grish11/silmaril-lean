module

public import Silmaril.Calculi.PERConstraints.Patterns.Defs
public import Silmaril.Calculi.PERConstraints.Congruence.Thms
public import Silmaril.Logic.Institution.Theory
import Silmaril.Proofs.Calculi.PERConstraints.Patterns

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns

open CategoryTheory Silmaril.Formats Silmaril.Logic.Institution

variable {base middle next : Congruence.Signature} {Hole : Type}
variable {source target : Signature}

@[simp] theorem Pattern.map_id (pattern : Pattern base Hole) : pattern.map (𝟙 base) = pattern :=
  Proofs.map_id pattern

theorem Pattern.map_comp (first : base ⟶ middle) (second : middle ⟶ next) (pattern : Pattern base Hole) :
    pattern.map (first ≫ second) = (pattern.map first).map second := Proofs.map_comp first second pattern

theorem Pattern.plug_map (rename : base ⟶ next) (tuple : Hole → base.carrier.Term) (pattern : Pattern base Hole) :
    (pattern.map rename).plug (rename.term ∘ tuple) = rename.term (pattern.plug tuple) :=
  Proofs.plug_map rename tuple pattern

theorem Pattern.enabled_map (rename : base ⟶ next) (tuple : Hole → base.carrier.Term) (pattern : Pattern base Hole)
    (enabled : pattern.Enabled tuple) : (pattern.map rename).Enabled (rename.term ∘ tuple) :=
  Proofs.enabled_map rename tuple pattern enabled

theorem Pattern.enabled_map_iff (rename : source ⟶ target) (tuple : Hole → source.base.carrier.Term)
    (pattern : Pattern source.base Hole) :
    (pattern.map rename.constructorMap).Enabled (rename.constructorMap.term ∘ tuple) ↔ pattern.Enabled tuple :=
  ⟨Proofs.enabled_of_map rename tuple pattern, pattern.enabled_map rename.constructorMap tuple⟩

theorem Pattern.plug_related {model : PER base.carrier.Term} (closed : base.constructors.Closed model)
    (pattern : Pattern base Hole) {left right : Hole → base.carrier.Term}
    (enabledLeft : pattern.Enabled left) (enabledRight : pattern.Enabled right)
    (related : ∀ index, model.rel (left index) (right index)) : model.rel (pattern.plug left) (pattern.plug right) :=
  Proofs.plug_related closed pattern enabledLeft enabledRight related

@[simp] theorem Rule.map_id (rule : Rule source) : rule.map (𝟙 source) = rule := by
  obtain ⟨arity, holeSort, output, pattern⟩ := rule
  exact congrArg (Rule.mk arity holeSort output) pattern.map_id

theorem Rule.map_comp {intermediate : Signature} (first : source ⟶ intermediate) (second : intermediate ⟶ target)
    (rule : Rule source) : rule.map (first ≫ second) = (rule.map first).map second := by
  obtain ⟨arity, holeSort, output, pattern⟩ := rule
  exact congrArg (Rule.mk arity (second.indexMap ∘ first.indexMap ∘ holeSort) (second.indexMap (first.indexMap output)))
    (pattern.map_comp first.constructorMap second.constructorMap)

@[simp] theorem reduct_id (family : Family source) : reduct (𝟙 source) family = family := rfl

theorem reduct_comp {intermediate : Signature} (first : source ⟶ intermediate) (second : intermediate ⟶ target)
    (family : Family target) : reduct (first ≫ second) family = reduct first (reduct second family) := rfl

theorem satisfaction (rename : source ⟶ target) (family : Family target) (rule : Rule source) :
    (rule.map rename).Holds family ↔ rule.Holds (reduct rename family) := Proofs.satisfaction rename family rule

theorem Rule.holds_of_compatible (rule : Rule source) (family : Family source)
    (closed : source.base.constructors.Closed (family rule.output))
    (compatible : ∀ index, family (rule.holeSort index) ≤ family rule.output) : rule.Holds family :=
  fun _ _ enabledLeft enabledRight related =>
    rule.pattern.plug_related closed enabledLeft enabledRight (fun index => compatible index (related index))

theorem Rule.holds_uniform (rule : Rule source) (model : Congruence.Model source.base) :
    rule.Holds (uniform source model) := rule.holds_of_compatible _ model.property (fun _ => le_rfl)

theorem uniform_reduct (rename : source ⟶ target) (model : Congruence.Model target.base) :
    reduct rename (uniform target model) = uniform source (Congruence.reduct (forget.map rename) model) := rfl

theorem uniform_injective (index : source.Index) : Function.Injective (uniform source) :=
  fun _ _ equal => Subtype.ext (congrFun equal index)

theorem satisfies_iff_semanticAt (rules : Set (Rule source)) (family : Family source) :
    Satisfies rules family ↔ ∀ index, SemanticAt rules family index :=
  ⟨fun holds _ rule chosen _ => holds rule chosen, fun holds rule chosen => holds rule.output rule chosen rfl⟩

theorem generated_extends (rules : Set (Rule source)) (seed : Family source) : Extends seed (generated rules seed) :=
  fun sort _ _ related model => model.property.1 sort related

theorem generated_satisfies (rules : Set (Rule source)) (seed : Family source) :
    Satisfies rules (generated rules seed) := Proofs.generated_satisfies rules seed

theorem generated_le {rules : Set (Rule source)} {seed family : Family source}
    (extendsSeed : Extends seed family) (satisfiesRules : Satisfies rules family) :
    Extends (generated rules seed) family :=
  fun _ _ _ related => related ⟨family, extendsSeed, satisfiesRules⟩

theorem generated_eq {rules : Set (Rule source)} {family : Family source} (holds : Satisfies rules family) :
    generated rules family = family :=
  funext fun sort => le_antisymm (generated_le (fun _ => le_rfl) holds sort) (generated_extends rules family sort)

def corridor (rename : source ⟶ target) : room source ⟶ room target :=
  ⟨Rule.map rename, Discrete.functor fun family => Discrete.mk (reduct rename family),
    fun model rule => satisfaction rename model.as rule⟩

def institution : Signature ⥤ Room.{0,0,0} where
  obj := room
  map := corridor
  map_id _ := by
    apply Room.hom_ext (funext Rule.map_id)
    exact Discrete.functor_ext (fun _ => rfl)
  map_comp first second := by
    apply Room.hom_ext (funext (Rule.map_comp first second))
    exact Discrete.functor_ext (fun _ => rfl)

def bundled : Inst := ⟨Signature, institution⟩

/-- Selected pattern systems form the existing category of institution
presentations: every selected source rule must map to a selected target rule. -/
abbrev System := Presentation institution

def System.Model (system : System) := {family : Family system.sig // Satisfies system.axioms family}

def System.reduct {system other : System} (rename : system ⟶ other) (model : other.Model) : system.Model :=
  ⟨Patterns.reduct rename.sig model.val,
    fun rule chosen => (satisfaction rename.sig model.val rule).1 (model.property _ (rename.mapsTo chosen))⟩

@[simp] theorem System.reduct_id {system : System} (model : system.Model) : System.reduct (𝟙 system) model = model := rfl

theorem System.reduct_comp {system middle other : System} (first : system ⟶ middle) (second : middle ⟶ other)
    (model : other.Model) : System.reduct (first ≫ second) model = System.reduct first (System.reduct second model) := rfl

def System.uniform (system : System) (model : Congruence.Model system.sig.base) : system.Model :=
  ⟨Patterns.uniform system.sig model, fun rule _ => rule.holds_uniform model⟩

def System.closure (system : System) (seed : Family system.sig) : system.Model :=
  ⟨generated system.axioms seed, generated_satisfies system.axioms seed⟩

end Silmaril.Calculi.PERConstraints.Patterns
