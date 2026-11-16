module

public import Silmaril.Logic.Separation.Parameterized.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized
open CategoryTheory Silmaril.Logic.Institution

structure Signature.Hom (A B : Signature) where
  operation : ∀ {n}, A.Op n → B.Op n
  atom : ∀ {n}, A.Atom n → B.Atom n

@[ext] theorem Signature.Hom.ext {A B : Signature} (f g : Signature.Hom A B)
    (ho : @f.operation = @g.operation) (ha : @f.atom = @g.atom) : f = g := by
  cases f; cases g; cases ho; cases ha; rfl

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id,id⟩
  comp f g := ⟨fun op => g.operation (f.operation op), fun a => g.atom (f.atom a)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {A B C : Signature}

def Term.map (f : A ⟶ B) {k} : Term A k → Term B k
  | .var i => .var i
  | .app op args => .app (f.operation op) (fun i => (args i).map f)

def Assertion.map (f : A ⟶ B) {k} : Assertion A k → Assertion B k
  | .eq t u => .eq (t.map f) (u.map f)
  | .atom a args => .atom (f.atom a) (fun i => (args i).map f)
  | .emp => .emp
  | .neg p => .neg (p.map f)
  | .conj p q => .conj (p.map f) (q.map f)
  | .sep p q => .sep (p.map f) (q.map f)
  | .wand p q => .wand (p.map f) (q.map f)

def Pattern.map (f : A ⟶ B) : {r k : Nat} → {P : Fin r → Nat} → Pattern A P k → Pattern B P k
  | _, _, _, .base p => .base (p.map f)
  | _, _, _, .pred i args => .pred i (fun j => (args j).map f)
  | _, _, _, .conj p q => .conj (p.map f) (q.map f)
  | _, _, _, .disj p q => .disj (p.map f) (q.map f)
  | _, _, _, .sep p q => .sep (p.map f) (q.map f)
  | _, _, _, .wand p q => .wand (p.map f) (q.map f)
  | _, _, _, .ex p => .ex (p.map f)
  | _, _, _, .all p => .all (p.map f)
  | _, _, _, .lfp body args => .lfp (body.map f) (fun j => (args j).map f)

/-- Value functions preserve operations; resource functions preserve the unit,
join relation and indexed atomic ownership. No injectivity premise is imposed. -/
structure Model.Hom (M N : Model A) where
  value : M.Value → N.Value
  resource : M.resource.carrier → N.resource.carrier
  operation : ∀ {n} (op : A.Op n) args,
    value (M.operation op args) = N.operation op (fun i => value (args i))
  unit : resource M.resource.unit = N.resource.unit
  join : ∀ {a b c}, M.resource.join a b c →
    N.resource.join (resource a) (resource b) (resource c)
  atom : ∀ {n} (a : A.Atom n) args {h}, h ∈ M.atom a args →
    resource h ∈ N.atom a (fun i => value (args i))

@[ext] theorem Model.Hom.ext {M N : Model A} (f g : Model.Hom M N)
    (hv : f.value = g.value) (hr : f.resource = g.resource) : f = g := by
  cases f; cases g; cases hv; cases hr; rfl

instance : Category (Model A) where
  Hom := Model.Hom
  id _ := {
    value := id
    resource := id
    operation := by intro n op args; rfl
    unit := rfl
    join := by intro a b c h; exact h
    atom := by intro n a args h hx; exact hx }
  comp f g := {
    value := g.value ∘ f.value
    resource := g.resource ∘ f.resource
    operation := by
      intro n op args
      change g.value (f.value (Model.operation _ op args)) = _
      rw [f.operation,g.operation]
      rfl
    unit := by change g.resource (f.resource _) = _; rw [f.unit,g.unit]
    join := fun h => g.join (f.join h)
    atom := by intro n a args h hx; exact g.atom a _ (f.atom a args hx) }
  id_comp _ := Model.Hom.ext _ _ rfl rfl
  comp_id _ := Model.Hom.ext _ _ rfl rfl
  assoc _ _ _ := Model.Hom.ext _ _ rfl rfl

abbrev reduct (f : A ⟶ B) (M : Model B) : Model A where
  Value := M.Value
  resource := M.resource
  operation op := M.operation (f.operation op)
  atom a := M.atom (f.atom a)

def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := ⟨h.value,h.resource,fun op args => h.operation (f.operation op) args,
    h.unit,h.join,by intro n a args r hr; exact h.atom (f.atom a) args hr⟩
  map_id _ := Model.Hom.ext _ _ rfl rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl rfl

end Silmaril.Logic.Separation.Parameterized
