module

public import Silmaril.Logic.Matching.FixedPoint.Thms

/-! Profile-preserving matching signature morphisms with arbitrary maps of sorts.
Carriers remain nonempty, as in the existing matching semantics. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory

abbrev SortedSignature := Algebraic.ManySorted.Signature

structure Signature where
  sorts : Type
  symbols : SortedSignature sorts

structure Hom (A B : Signature) where
  sorts : A.sorts → B.sorts
  operations : ∀ {n inputs output}, A.symbols.operations n inputs output →
    B.symbols.operations n (sorts ∘ inputs) (sorts output)

namespace Hom
variable {A B C : Signature}
def id (A : Signature) : Hom A A := ⟨fun s => s, fun op => op⟩
def comp (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨g.sorts ∘ f.sorts, fun op => g.operations (f.operations op)⟩

/-- Sort changes reindex actual carriers, not just symbol names. -/
def reduct (f : Hom A B) (M : FirstOrder.Model B.symbols) : FirstOrder.Model A.symbols where
  carrier s := M.carrier (f.sorts s)
  nonempty s := M.nonempty (f.sorts s)
  operation op args := M.operation (f.operations op) args

def reductFunctor (f : Hom A B) : FirstOrder.Model B.symbols ⥤ FirstOrder.Model A.symbols where
  obj := reduct f
  map h := ⟨fun s => h.map (f.sorts s), fun op args result member =>
    h.operation (f.operations op) args result member⟩
  map_id _ := FirstOrder.Model.Hom.ext _ _ rfl
  map_comp _ _ := FirstOrder.Model.Hom.ext _ _ rfl

/-- Binder transport for a sort-reindexed context. -/
theorem map_cons (f : Hom A B) {k : Nat} (bound : A.sorts) (Γ : Fin k → A.sorts) :
    f.sorts ∘ Fin.cases bound Γ = Fin.cases (f.sorts bound) (f.sorts ∘ Γ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def pattern (f : Hom A B) {k : Nat} {Γ : Fin k → A.sorts} {s : A.sorts} :
    FirstOrder.Pattern A.symbols Γ s →
      FirstOrder.Pattern B.symbols (f.sorts ∘ Γ) (f.sorts s)
  | .var i => .var i
  | .app op args => .app (f.operations op) (fun i => pattern f (args i))
  | .neg p => .neg (pattern f p)
  | .conj p q => .conj (pattern f p) (pattern f q)
  | .ex bound body => .ex (f.sorts bound) ((map_cons f bound Γ) ▸ pattern f body)

/-- Existing finite contexts and result sorts are both reindexed. -/
def sentence (f : Hom A B) (p : FirstOrder.Sentence A.symbols) : FirstOrder.Sentence B.symbols :=
  ⟨p.variableCount, f.sorts ∘ p.context, f.sorts p.sort, pattern f p.pattern⟩

end Hom
end Silmaril.Logic.Matching.SortMaps

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory
instance : Category Signature where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl
end Silmaril.Logic.Matching.SortMaps

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps.Hom
variable {A B : Signature}
/-- Both object and set-variable sorts change; μ/ν retain native unary semantics. -/
def fixedPattern (f : Hom A B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    FixedPoint.Pattern B.symbols (f.sorts ∘ P) (f.sorts ∘ Γ) (f.sorts s) := by
  induction p with
  | base p => exact .base (pattern f p)
  | setvar i => exact .setvar i
  | app op args ih => exact .app (f.operations op) ih
  | dualApp op args ih => exact .dualApp (f.operations op) ih
  | conj p q hp hq => exact .conj hp hq
  | disj p q hp hq => exact .disj hp hq
  | ex bound p hp => exact .ex (f.sorts bound) ((map_cons f bound _) ▸ hp)
  | all bound p hp => exact .all (f.sorts bound) ((map_cons f bound _) ▸ hp)
  | mu p hp => exact .mu hp
  | nu p hp => exact .nu hp

def fixedSentence (f : Hom A B) (p : FixedPoint.Sentence A.symbols) : FixedPoint.Sentence B.symbols :=
  ⟨p.setCount, p.objectCount, f.sorts ∘ p.sets, f.sorts ∘ p.objects,
    f.sorts p.sort, fixedPattern f p.pattern⟩
end Silmaril.Logic.Matching.SortMaps.Hom
