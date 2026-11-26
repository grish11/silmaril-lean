module

public import Silmaril.SSA.MLIR.SCF.LetIter.FixedProfile.Observation

/-! # Observational institutions over typed opcode signatures

Both presentations use equations and refinements of programs modulo complete
observations over typed inputs and evaluators. Model reduct precomposes an
evaluator with the opcode map.
-/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.FixedProfile

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational (Sentence)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Eval)

variable {P : Profile} {S T U : Signature}

/-- The shared institution construction takes independently given syntax,
renaming, and observations. -/
structure Presentation (P : Profile) where
  Prog : Signature → Type
  rename : {S T : Signature} → (S ⟶ T) → Prog S → Prog T
  observe : {S : Signature} → Prog S → Eval S.op → Env P.input → Set (Answer P)
  rename_id : ∀ {S : Signature} (p : Prog S), rename (𝟙 S) p = p
  rename_comp : ∀ {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) (p : Prog S),
    rename g (rename f p) = rename (f ≫ g) p
  observe_rename : ∀ {S T : Signature} (f : S ⟶ T) (p : Prog S) (M : Eval T.op) (input : Env P.input),
    observe (rename f p) M input = observe p (reduct f M) input

/-- The source uses the independently defined typed SCF semantics. -/
def scalarPresentation (P : Profile) : Presentation P where
  Prog := Scalar P
  rename := Scalar.rename
  observe := Scalar.observe
  rename_id := Scalar.rename_id
  rename_comp := Scalar.rename_comp
  observe_rename := Scalar.observe_rename

/-- The target uses admitted native syntax and native LetIter semantics. -/
def nativePresentation (P : Profile) : Presentation P where
  Prog := Native P
  rename := Native.rename
  observe := Native.observe
  rename_id := Native.rename_id
  rename_comp := Native.rename_comp
  observe_rename := Native.observe_rename

namespace Presentation

variable (L : Presentation P)

/-- Quotient by equality of all returns and divergence at every model and input. -/
abbrev obsSetoid (S : Signature) : Setoid (L.Prog S) where
  r a b := ∀ (M : Eval S.op) (input : Env P.input), L.observe a M input = L.observe b M input
  iseqv := ⟨fun _ _ _ => rfl, fun h M input => (h M input).symm,
    fun h₁ h₂ M input => (h₁ M input).trans (h₂ M input)⟩

abbrev Program (S : Signature) := Quotient (L.obsSetoid S)

def observeQ (p : L.Program S) (M : Eval S.op) (input : Env P.input) : Set (Answer P) :=
  Quotient.liftOn p (fun raw => L.observe raw M input) (by
    intro a b h
    exact (show ∀ (N : Eval S.op) (ρ : Env P.input), L.observe a N ρ = L.observe b N ρ from h) M input)

def renameQ (f : S ⟶ T) : L.Program S → L.Program T :=
  Quotient.map (L.rename f) (fun a b h M input => by
    rw [L.observe_rename f a, L.observe_rename f b]
    exact h (reduct f M) input)

theorem renameQ_id (p : L.Program S) : L.renameQ (𝟙 S) p = p :=
  Quotient.inductionOn p (fun a => congrArg Quotient.mk'' (L.rename_id a))

theorem renameQ_comp (f : S ⟶ T) (g : T ⟶ U) (p : L.Program S) :
    L.renameQ g (L.renameQ f p) = L.renameQ (f ≫ g) p :=
  Quotient.inductionOn p (fun a => congrArg Quotient.mk'' (L.rename_comp f g a))

theorem observeQ_rename (f : S ⟶ T) (p : L.Program S) (M : Eval T.op) (input : Env P.input) :
    L.observeQ (L.renameQ f p) M input = L.observeQ p (reduct f M) input :=
  Quotient.inductionOn p (fun a => L.observe_rename f a M input)

end Presentation

/-- Contravariant action on the discrete categories of primitive evaluators. -/
def modelReduct (f : S ⟶ T) : Discrete (Eval T.op) ⥤ Discrete (Eval S.op) :=
  Discrete.functor (fun M => Discrete.mk (reduct f M))

theorem modelReduct_id (S : Signature) : modelReduct (𝟙 S) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun M => by cases M; rfl)

theorem modelReduct_comp (f : S ⟶ T) (g : T ⟶ U) :
    modelReduct (f ≫ g) = modelReduct g ⋙ modelReduct f :=
  CategoryTheory.Functor.ext (fun M => by cases M; rfl)

namespace Presentation

variable (L : Presentation P)

/-- Sen is observational equations and refinements. Mod is discrete on
opcode evaluators. Sat compares the answer sets at every typed input. -/
def room (S : Signature) : Room.{0, 0, 0} where
  Sen := Sentence (L.Program S)
  Mod := Cat.of (Discrete (Eval S.op))
  Sat M φ := ∀ input, φ.Holds (fun p => L.observeQ p M.as input)

theorem satisfaction (f : S ⟶ T) (M : Eval T.op) (φ : Sentence (L.Program S)) :
    (L.room T).Sat ⟨M⟩ (φ.map (L.renameQ f)) ↔ (L.room S).Sat ⟨reduct f M⟩ φ := by
  change (∀ input, (φ.map (L.renameQ f)).Holds (fun p => L.observeQ p M input)) ↔
    ∀ input, φ.Holds (fun p => L.observeQ p (reduct f M) input)
  cases φ <;> simp only [Sentence.map, Sentence.Holds, L.observeQ_rename]

def corridor (f : S ⟶ T) : L.room S ⟶ L.room T :=
  ⟨Sentence.map (L.renameQ f), modelReduct f, fun M => L.satisfaction f M.as⟩

theorem corridor_id (S : Signature) : L.corridor (𝟙 S) = 𝟙 (L.room S) := by
  apply Room.hom_ext
  · change Sentence.map (L.renameQ (𝟙 S)) = id
    rw [show L.renameQ (𝟙 S) = id from funext L.renameQ_id, Sentence.map_id]
  · exact modelReduct_id S

theorem corridor_comp (f : S ⟶ T) (g : T ⟶ U) : L.corridor (f ≫ g) = L.corridor f ≫ L.corridor g := by
  apply Room.hom_ext
  · change Sentence.map (L.renameQ (f ≫ g)) = Sentence.map (L.renameQ g) ∘ Sentence.map (L.renameQ f)
    rw [Sentence.map_comp]
    exact congrArg Sentence.map (funext fun p => (L.renameQ_comp f g p).symm)
  · exact modelReduct_comp f g

def inst : Inst.{1, 0, 0, 0, 0} where
  Sign := Signature
  I := ⟨L.room, L.corridor, L.corridor_id, L.corridor_comp⟩

end Presentation

/-- Typed scalar SCF modulo the specified observations. -/
def scalarInstitution (P : Profile) := (scalarPresentation P).inst

/-- Admitted native one-iteration LetIter modulo the specified observations. -/
def nativeInstitution (P : Profile) := (nativePresentation P).inst

end Silmaril.MLIR.SCF.LetIter.FixedProfile
