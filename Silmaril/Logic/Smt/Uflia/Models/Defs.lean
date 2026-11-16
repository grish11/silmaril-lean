module

public import Silmaril.Logic.Smt.Uflia.Thms

/-! Model maps fix Bool and Int, preserve uninterpreted operations, and may map
user carriers noninjectively. Injective maps are a separate category. Logical
equality is not an uninterpreted operation: arbitrary homomorphisms need not
reflect equality or preserve negated assertions. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia
open CategoryTheory

namespace Carriers

/-- A user-carrier map acts identically on both interpreted sorts. -/
def mapValue {U : Type} {C D : Carriers U}
    (f : ∀ u, C.user u → D.user u) : (s : SortCode U) → C.value s → D.value s
  | .bool => id
  | .int => id
  | .user u => f u

@[simp] theorem mapValue_id {U : Type} (C : Carriers U) (s : SortCode U)
    (x : C.value s) : mapValue (fun _ => id) s x = x := by
  cases s <;> rfl

@[simp] theorem mapValue_comp {U : Type} {C D E : Carriers U}
    (f : ∀ u, C.user u → D.user u) (g : ∀ u, D.user u → E.user u)
    (s : SortCode U) (x : C.value s) :
    mapValue (fun u => g u ∘ f u) s x = mapValue g s (mapValue f s x) := by
  cases s <;> rfl

theorem mapValue_injective {U : Type} {C D : Carriers U}
    (f : ∀ u, C.user u → D.user u) (injective : ∀ u, Function.Injective (f u))
    (s : SortCode U) : Function.Injective (mapValue f s) := by
  cases s with
  | bool => exact Function.injective_id
  | int => exact Function.injective_id
  | user u => exact injective u

end Carriers

/-- Sorted algebra homomorphisms for the UF signature, fixing Bool and Int.
No injectivity, surjectivity or preservation of arbitrary formulas is assumed. -/
structure Model.Hom {U : Type} {A : Signature U} (M N : Model A) where
  user : ∀ u, M.carriers.user u → N.carriers.user u
  operation : ∀ {n inputs output} (symbol : A.operations n inputs output)
    (args : (i : Fin n) → M.carriers.value (inputs i)),
    Carriers.mapValue user output (M.operation symbol args) =
      N.operation symbol (fun i => Carriers.mapValue user (inputs i) (args i))

namespace Model.Hom
variable {U : Type} {A : Signature U} {M N P Q : Model A}

def value (h : Hom M N) : (s : SortCode U) → M.carriers.value s → N.carriers.value s :=
  Carriers.mapValue h.user

@[ext] theorem ext (f g : Hom M N) (same : f.user = g.user) : f = g := by
  cases f
  cases g
  cases same
  rfl

def identity (M : Model A) : Hom M M where
  user _ := id
  operation symbol args := by
    rw [Carriers.mapValue_id]
    congr 1
    funext i
    exact (Carriers.mapValue_id _ _ _).symm

def comp (f : Hom M N) (g : Hom N P) : Hom M P where
  user u := g.user u ∘ f.user u
  operation symbol args := by
    rw [Carriers.mapValue_comp, f.operation, g.operation]
    congr 1
    funext i
    exact (Carriers.mapValue_comp f.user g.user _ _).symm

/-- Restriction changes operation names and keeps the entire carrier map. -/
def reduct {B : Signature U} (f : A ⟶ B) {M N : Model B}
    (h : Hom M N) : Hom (M.reduct f) (N.reduct f) where
  user := h.user
  operation symbol args := h.operation (f.operations symbol) args

end Model.Hom

instance {U : Type} {A : Signature U} : Category (Model A) where
  Hom := Model.Hom
  id := Model.Hom.identity
  comp := Model.Hom.comp
  id_comp _ := Model.Hom.ext _ _ rfl
  comp_id _ := Model.Hom.ext _ _ rfl
  assoc _ _ _ := Model.Hom.ext _ _ rfl

/-- Reduct is a functor on actual homomorphisms, including noninjective maps. -/
def Model.reductFunctor {U : Type} {A B : Signature U} (f : A ⟶ B) :
    Model B ⥤ Model A where
  obj := Model.reduct f
  map := Model.Hom.reduct f
  map_id _ := Model.Hom.ext _ _ rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl

/-- An embedding additionally reflects equality in every user sort. -/
structure Model.Embedding {U : Type} {A : Signature U} (M N : Model A) extends Model.Hom M N where
  injective : ∀ u, Function.Injective (user u)

namespace Model.Embedding
variable {U : Type} {A : Signature U} {M N P : Model A}

@[ext] theorem ext (f g : Embedding M N) (same : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases same
  rfl

def identity (M : Model A) : Embedding M M :=
  ⟨Model.Hom.identity M, fun _ => Function.injective_id⟩

def comp (f : Embedding M N) (g : Embedding N P) : Embedding M P :=
  ⟨Model.Hom.comp f.toHom g.toHom, fun u => (g.injective u).comp (f.injective u)⟩

def reduct {B : Signature U} (f : A ⟶ B) {M N : Model B}
    (h : Embedding M N) : Embedding (M.reduct f) (N.reduct f) :=
  ⟨h.toHom.reduct f, h.injective⟩

end Model.Embedding

/-- A wrapper selects embeddings as arrows without changing any model data. -/
structure EmbeddingModel {U : Type} (A : Signature U) where
  model : Model A

instance {U : Type} {A : Signature U} : Category (EmbeddingModel A) where
  Hom M N := Model.Embedding M.model N.model
  id M := Model.Embedding.identity M.model
  comp := Model.Embedding.comp
  id_comp _ := Model.Embedding.ext _ _ (Model.Hom.ext _ _ rfl)
  comp_id _ := Model.Embedding.ext _ _ (Model.Hom.ext _ _ rfl)
  assoc _ _ _ := Model.Embedding.ext _ _ (Model.Hom.ext _ _ rfl)

def EmbeddingModel.reduct {U : Type} {A B : Signature U} (f : A ⟶ B) :
    EmbeddingModel B ⥤ EmbeddingModel A where
  obj M := ⟨M.model.reduct f⟩
  map := Model.Embedding.reduct f
  map_id _ := Model.Embedding.ext _ _ (Model.Hom.ext _ _ rfl)
  map_comp _ _ := Model.Embedding.ext _ _ (Model.Hom.ext _ _ rfl)

/-- Forget only injectivity; every carrier function and operation law is retained. -/
def EmbeddingModel.forget {U : Type} (A : Signature U) : EmbeddingModel A ⥤ Model A where
  obj := EmbeddingModel.model
  map := Model.Embedding.toHom
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.Smt.Uflia
