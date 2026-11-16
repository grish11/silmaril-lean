module

public import Silmaril.Logic.Smt.Uflia.Quantified.Models.Institution.Defs

/-! SMT signature maps may change user sorts while fixing Bool and Int.
They can also instantiate a user sort by Bool or Int. Their reducts retain the
ordinary UF homomorphisms; logical truth is related by signature reduct, not by
arbitrary model homomorphisms. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps
open CategoryTheory Silmaril.Logic.Algebraic

structure Signature where
  users : Type
  symbols : Uflia.Signature users

/-- Every symbol's complete arity and sort profile is transported. -/
structure Hom (A B : Signature) where
  sorts : SortCode A.users → SortCode B.users
  bool : sorts .bool = .bool
  int : sorts .int = .int
  operations : ∀ {n inputs output}, A.symbols.operations n inputs output →
    B.symbols.operations n (sorts ∘ inputs) (sorts output)

namespace Hom
variable {A B C : Signature}

def identity (A : Signature) : Hom A A := ⟨id, rfl, rfl, fun op => op⟩

def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  sorts := g.sorts ∘ f.sorts
  bool := (congrArg g.sorts f.bool).trans g.bool
  int := (congrArg g.sorts f.int).trans g.int
  operations op := g.operations (f.operations op)

end Hom

instance : Category Signature where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

namespace Hom
variable {A B C : Signature}

abbrev carriers (f : A ⟶ B) (M : Model B.symbols) : Carriers A.users where
  user u := M.carriers.value (f.sorts (.user u))
  nonempty u := by
    cases hs : f.sorts (.user u) with
    | bool => exact ⟨false⟩
    | int => exact ⟨0⟩
    | user v => exact M.carriers.nonempty v

/-- Reindexing fixes the actual Bool/Int types and selects the target carrier
for each user sort. This equivalence only performs equality transport. -/
def value (f : A ⟶ B) (M : Model B.symbols) (s : SortCode A.users) :
    (carriers f M).value s ≃ M.carriers.value (f.sorts s) :=
  Equiv.cast (by cases s with
    | bool => exact congrArg M.carriers.value f.bool.symm
    | int => exact congrArg M.carriers.value f.int.symm
    | user _ => rfl)

abbrev reduct (f : A ⟶ B) (M : Model B.symbols) : Model A.symbols where
  carriers := carriers f M
  operation {_n inputs output} op args :=
    (value f M output).symm (M.operation (f.operations op)
      (fun i => value f M (inputs i) (args i)))

def hom (f : A ⟶ B) {M N : Model B.symbols} (h : M ⟶ N) :
    reduct f M ⟶ reduct f N where
  user u := h.value (f.sorts (.user u))
  operation {_n inputs output} op args := by
    apply (value f N output).injective
    have transport {s t : SortCode B.users} (e : s = t) (y : M.carriers.value s) :
        Equiv.cast (congrArg N.carriers.value e) (h.value s y) =
          h.value t (Equiv.cast (congrArg M.carriers.value e) y) := by
      cases e
      rfl
    have natural (s : SortCode A.users) (x : (carriers f M).value s) :
        value f N s (Carriers.mapValue (fun u => h.value (f.sorts (.user u))) s x) =
          h.value (f.sorts s) (value f M s x) := by
      cases s with
      | bool =>
          exact transport f.bool.symm x
      | int =>
          exact transport f.int.symm x
      | user u => rfl
    change value f N output
      (Carriers.mapValue (fun u => h.value (f.sorts (.user u))) output
        ((value f M output).symm _)) =
      value f N output ((value f N output).symm _)
    rw [natural]
    rw [Equiv.apply_symm_apply]
    change Carriers.mapValue h.user (f.sorts output) (M.operation (f.operations op) _) = _
    rw [h.operation]
    rw [Equiv.apply_symm_apply]
    congr 1
    funext i
    exact (natural (inputs i) (args i)).symm

def reductFunctor (f : A ⟶ B) : Model B.symbols ⥤ Model A.symbols where
  obj := reduct f
  map := hom f
  map_id M := by
    apply Model.Hom.ext
    funext u x
    change (Model.Hom.identity M).value (f.sorts (.user u)) x = x
    have same (s : SortCode B.users) (y : M.carriers.value s) :
        (Model.Hom.identity M).value s y = y := by cases s <;> rfl
    exact same _ _
  map_comp h k := by
    apply Model.Hom.ext
    funext u x
    change (Model.Hom.comp h k).value (f.sorts (.user u)) x =
      k.value (f.sorts (.user u)) (h.value (f.sorts (.user u)) x)
    have same (s : SortCode B.users) (y : _) :
        (Model.Hom.comp h k).value s y = k.value s (h.value s y) := by cases s <;> rfl
    exact same _ _

end Hom
end Silmaril.Logic.Smt.Uflia.SortMaps
