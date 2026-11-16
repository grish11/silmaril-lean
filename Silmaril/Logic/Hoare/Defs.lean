module

public import Silmaril.Logic.PDL
public import Silmaril.Logic.Reachability

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare
open CategoryTheory Silmaril.Logic.Institution
variable (C : Type)

/-- Named commands have actual regular-program bodies, not uninterpreted repeated steps. -/
structure Signature where
  language : PDL.Signature
  body : C → PDL.Program language

structure Signature.Hom (A B : Signature C) where
  language : A.language ⟶ B.language
  body : ∀ c, (A.body c).map language = B.body c

@[ext] theorem Signature.Hom.ext {A B : Signature C} (f g : Signature.Hom C A B)
    (h : f.language = g.language) : f = g := by cases f; cases g; cases h; rfl

instance : Category (Signature C) where
  Hom := Signature.Hom C
  id A := ⟨𝟙 A.language, fun c => PDL.Program.map_id (A.body c)⟩
  comp f g := ⟨f.language ≫ g.language, fun c => by
    rw [PDL.Program.map_comp, f.body c, g.body c]⟩
  id_comp f := Signature.Hom.ext C _ _ (Category.id_comp _)
  comp_id f := Signature.Hom.ext C _ _ (Category.comp_id _)
  assoc f g h := Signature.Hom.ext C _ _ (Category.assoc _ _ _)

abbrev Model (A : Signature C) := PDL.Model A.language

structure Triple (A : Signature C) where
  command : C
  pre : PDL.Formula A.language
  post : PDL.Formula A.language

/-- Ordinary relational partial correctness: only completed command executions matter. -/
def Triple.Satisfies {A : Signature C} (M : Model C A) (t : Triple C A) : Prop :=
  ∀ w, t.pre.Holds M w → ∀ v, (A.body t.command).Rel M w v → t.post.Holds M v

def Triple.map {A B : Signature C} (f : A ⟶ B) (t : Triple C A) : Triple C B :=
  ⟨t.command, t.pre.map f.language, t.post.map f.language⟩

/-- None is an unused configuration component, so even the empty command interface has models. -/
abbrev Phase (W : Type) := Option C × Bool × W

def phaseStep {A : Signature C} (M : Model C A) (x y : Phase C M.World) : Prop :=
  ∃ c, x.1 = some c ∧ x.2.1 = false ∧ y.1 = some c ∧
    ((y.2.1 = true ∧ (A.body c).Rel M x.2.2 y.2.2) ∨
      (y = x ∧ ¬ ∃ v, (A.body c).Rel M x.2.2 v))

/-- Explicit entry/exit labels; assertions are evaluated on the underlying state. -/
abbrev Label (A : Signature C) := C × Bool × PDL.Formula A.language

abbrev reachSignaturesObj (A : Signature C) : Reachability.Signature () :=
  Reachability.relationalSignature (Label C A)

def labelMap {A B : Signature C} (f : A ⟶ B) (a : Label C A) : Label C B :=
  (a.1, a.2.1, a.2.2.map f.language)

def reachSignaturesMap {A B : Signature C} (f : A ⟶ B) : reachSignaturesObj C A ⟶ reachSignaturesObj C B :=
  ⟨Matching.FixedPoint.modalSignatureMap ⟨labelMap C f, id⟩, rfl⟩

def reachSignatures : Signature C ⥤ Reachability.Signature () where
  obj := reachSignaturesObj C
  map := reachSignaturesMap C
  map_id A := by
    apply Reachability.Signature.Hom.ext
    apply Algebraic.ManySorted.Signature.Hom.ext
    intro n inputs output op
    cases op with
    | atom a => exact congrArg Matching.FixedPoint.ModalOperation.atom (by
        rcases a with ⟨c, b, p⟩; exact congrArg (fun q => (c,b,q)) (PDL.Formula.map_id p))
    | action => rfl
  map_comp f g := by
    apply Reachability.Signature.Hom.ext
    apply Algebraic.ManySorted.Signature.Hom.ext
    intro n inputs output op
    cases op with
    | atom a => exact congrArg Matching.FixedPoint.ModalOperation.atom (by
        rcases a with ⟨c,b,p⟩; exact congrArg (fun q => (c,b,q)) (PDL.Formula.map_comp f.language g.language p))
    | action => rfl

/-- Operational shape of the constrained target, with no satisfaction premise stored. -/
def expand {A : Signature C} (M : Model C A) : Reachability.Model () (reachSignaturesObj C A) :=
  @Reachability.relationalModel (Label C A) (Phase C M.World) ⟨(none, false, M.point)⟩
    (phaseStep C M) (fun a => {x | x.1 = some a.1 ∧ x.2.1 = a.2.1 ∧ a.2.2.Holds M x.2.2})

def encode {A : Signature C} (t : Triple C A) : Reachability.Sentence () (reachSignaturesObj C A) :=
  Reachability.atomRule .allPath (t.command, false, t.pre) (t.command, true, t.post)

end Silmaril.Logic.Hoare
