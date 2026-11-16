module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Model.Defs
public import Silmaril.Logic.Matching.SortMaps.Thms

/-! Varying scope signatures, designated builtin names and declaration labels.
Models constructs restricted builtin reducts; Institution provides the full
typed Boolean/fixed-point institution. Raw source transport is separate. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
open CategoryTheory

/-- Each endpoint chooses its own builtin sort names and actual finite scope. -/
structure Signature where
  bindings : SortBindings
  scope : Kore.Modules.Scope
  literalPrefix : String
  literals : List LiteralBinding
  hooks : List HookBinding

abbrev Signature.native (A : Signature) : Matching.SortMaps.Signature :=
  ⟨String, A.scope.signature⟩

inductive Label where
  | literal : Literal → Label
  | hook : Hook → Label

/-- Labels use actual declaration identity, not just printed names. There is no
synthetic default literal or hook for a declaration missing its binding. -/
def Signature.labels (A : Signature) (op : Kore.Modules.NamedSymbol) : Set Label :=
  {tag | match tag with
    | .literal l => ∃ b ∈ A.literals, b.symbol = op ∧ b.literal = l
    | .hook h => ∃ b ∈ A.hooks, b.symbol = op ∧ b.hook = h}

structure Hom (A B : Signature) where
  native : A.native ⟶ B.native
  integer : native.sorts A.bindings.intSort = B.bindings.intSort
  boolean : native.sorts A.bindings.boolSort = B.bindings.boolSort
  labels : ∀ {n inputs output} (op : A.scope.signature.operations n inputs output),
    A.labels op.val ⊆ B.labels (native.operations op).val

namespace Hom
variable {A B C : Signature}

def id (A : Signature) : Hom A A :=
  ⟨𝟙 A.native, rfl, rfl, fun _ _ member => member⟩

def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  native := f.native ≫ g.native
  integer := (congrArg g.native.sorts f.integer).trans g.integer
  boolean := (congrArg g.native.sorts f.boolean).trans g.boolean
  labels op _ member := g.labels (f.native.operations op) (f.labels op member)

@[ext] theorem ext {f g : Hom A B} (same : f.native = g.native) : f = g := by
  cases f
  cases g
  cases same
  rfl
end Hom

instance : Category Signature where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.native)
  comp_id f := Hom.ext (Category.comp_id f.native)
  assoc f g h := Hom.ext (Category.assoc f.native g.native h.native)

/-- Forget only labels and designated names, retaining the exact sort and
operation map. Noninjective ordinary-name maps are permitted. -/
def nativeSignatures : Signature ⥤ Matching.SortMaps.Signature where
  obj := Signature.native
  map := Hom.native
  map_id _ := rfl
  map_comp _ _ := rfl

namespace Hom
variable {A B : Signature}

abbrev nativeReduct (f : A ⟶ B) (M : Matching.FirstOrder.Model B.scope.signature) :=
  Matching.SortMaps.Hom.reduct f.native M

abbrev nativeReductFunctor (f : A ⟶ B) :=
  Matching.SortMaps.Hom.reductFunctor f.native

/-- An actual varying-carrier satisfaction theorem for the existing positive
fixed-point sublanguage. It does not assert general Boolean or raw transport. -/
theorem positive_satisfaction (f : A ⟶ B)
    (M : Matching.FirstOrder.Model B.scope.signature)
    (p : Matching.FixedPoint.Sentence A.scope.signature) :
    Matching.FixedPoint.Sentence.Satisfies M
      (Matching.SortMaps.Hom.fixedSentence f.native p) ↔
      Matching.FixedPoint.Sentence.Satisfies (nativeReduct f M) p :=
  Matching.SortMaps.Hom.fixedSatisfaction f.native M p

/-- Distinct designated carriers cannot be identified by an admitted map. -/
theorem builtin_images_distinct (f : A ⟶ B) :
    f.native.sorts A.bindings.intSort ≠ f.native.sorts A.bindings.boolSort := by
  rw [f.integer, f.boolean]
  exact B.bindings.distinct

end Hom
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
