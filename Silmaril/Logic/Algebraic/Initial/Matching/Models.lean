module

public import Silmaril.Logic.Algebraic.Initial.Matching.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching
open CategoryTheory Silmaril.Logic.Institution.Examples

theorem Model.constructor_mem_iff {A : Signature} (M : Model A)
    {n : Nat} {w : Fin n → Unit} {s : Unit} (op : A.Op n)
    (args : ∀ i, M.native.carrier (w i)) (value : M.native.carrier s) :
    value ∈ M.native.operation (.constructor op) args ↔ value = M.decode.op op args := by
  constructor
  · exact (Classical.choose_spec (M.constructor op args)).2 value
  · intro h
    subst value
    exact (Classical.choose_spec (M.constructor op args)).1

def Model.decodeHom {A : Signature} {M N : Model A} (f : M ⟶ N) : M.decode ⟶ N.decode where
  map := f.map
  map_op := by
    intro n w s op args
    apply (N.constructor_mem_iff op _ _).1
    apply f.operation (.constructor op)
    exact (M.constructor_mem_iff op args _).2 rfl

def decodeFunctor (A : Signature) : Model A ⥤ EQ.Algebra A.public where
  obj := Model.decode
  map := Model.decodeHom
  map_id _ := Initial.algebraHom_ext _ _ rfl
  map_comp _ _ := Initial.algebraHom_ext _ _ rfl

def expandHom {A : Signature} {M N : EQ.Algebra A.public} (f : M ⟶ N) : expand M ⟶ expand N where
  map := f.map
  operation := by
    intro n w s op args value h
    cases op with
    | constructor op =>
      change value = M.op op args at h
      change f.map s value = N.op op (fun i => f.map (w i) (args i))
      exact h ▸ f.map_op op args
    | ceil => trivial

def expandFunctor (A : Signature) : EQ.Algebra A.public ⥤ Model A where
  obj := expand
  map := expandHom
  map_id _ := Silmaril.Logic.Matching.FirstOrder.Model.Hom.ext _ _ rfl
  map_comp _ _ := Silmaril.Logic.Matching.FirstOrder.Model.Hom.ext _ _ rfl

def Model.reduct {A B : Signature} (f : A ⟶ B) (M : Model B) : Model A where
  native := Silmaril.Logic.Matching.FirstOrder.SignatureMap.reduct (nativeMap f) M.native
  constructor op args := M.constructor (f.operations op) args
  ceil args := M.ceil args

def reductFunctor {A B : Signature} (f : A ⟶ B) : Model B ⥤ Model A where
  obj := Model.reduct f
  map h := ⟨h.map, fun op args value member => h.operation ((nativeMap f).operations op) args value member⟩
  map_id _ := Silmaril.Logic.Matching.FirstOrder.Model.Hom.ext _ _ rfl
  map_comp _ _ := Silmaril.Logic.Matching.FirstOrder.Model.Hom.ext _ _ rfl

/-- Decoding the canonical singleton expansion recovers every actual operation. -/
theorem decode_expand {A : Signature} (M : EQ.Algebra A.public) : (expand M).decode = M := by
  cases M with
  | mk carrier op =>
    dsimp only [expand, Model.decode]
    congr 1
    funext n w s c args
    exact ((Classical.choose_spec ((expand { carrier := carrier, op := op }).constructor
      (w := w) (s := s) c args)).2 (@op n w s c args) rfl).symm


/-- The native operation graphs are reconstructed from their unique values. -/
theorem expand_decode_native {A : Signature} (M : Model A) : (expand M.decode).native = M.native := by
  cases M with
  | mk native ctor ceil =>
    cases native with
    | mk carrier inhabited operation =>
      dsimp only [expand, Model.decode]
      congr 1
      funext n w s op args
      cases op with
      | constructor c =>
        ext value
        exact ((Model.constructor_mem_iff ⟨⟨carrier, inhabited, operation⟩, ctor, ceil⟩ c args value)).symm
      | ceil => exact (ceil args).symm

end Silmaril.Logic.Algebraic.Initial.Matching
