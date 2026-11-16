module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Source.Thms
public import Silmaril.Logic.Smt.Uflia.Quantified.Script.Thms

/-! Whole accepted scripts over genuine varying-sort signatures. The existing
reader, command layout and assertion decoder are reused without a new grammar. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Source.Script
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- A finite quantified problem over any ambient sort type. Order and duplicate
assertions remain in the syntax; every assertion uses the same supplied model. -/
abbrev Problem (A : Signature) := List (Quantified.Sentence A.symbols)

namespace Problem
variable {A B C : Signature}

def Holds (M : Model A.symbols) (p : Problem A) : Prop :=
  ∀ sentence ∈ p, sentence.Holds M

def map (f : A ⟶ B) (p : Problem A) : Problem B :=
  List.map (Hom.quantifiedSentence f) p

@[simp] theorem map_id (p : Problem A) : map (𝟙 A) p = p := by
  induction p with
  | nil => rfl
  | cons sentence rest ih =>
      simpa only [map, List.map_cons, Hom.quantifiedSentence_id] using
        congrArg (List.cons sentence) ih

@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Problem A) :
    map (f ≫ g) p = map g (map f p) := by
  simp only [map, List.map_map]
  congr 1
  funext sentence
  exact Hom.quantifiedSentence_comp f g sentence

theorem holds_map (f : A ⟶ B) (M : Model B.symbols) (p : Problem A) :
    Holds M (map f p) ↔ Holds (Hom.reduct f M) p := by
  simp only [Holds, map, List.forall_mem_map, Hom.holds_quantifiedSentence]

def room (A : Signature) : Room.{0,0,1} :=
  ⟨Problem A, Cat.of (Model A.symbols), Holds⟩

def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨map f, Hom.reductFunctor f, holds_map f⟩

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext map_id) (Hom.model_reductFunctor_id A)
  map_comp f g := Room.hom_ext (funext (map_comp f g)) (Hom.model_reductFunctor_comp f g)

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩
end Problem

/-- A single quantified sentence becomes a singleton finite problem; every
ordinary model and model homomorphism is retained. -/
def singleton : Inst.CoHom QuantifiedModels.inst Problem.inst where
  Φ := 𝟭 Signature
  ρ :=
    { app A := ⟨(fun sentence => [sentence]), 𝟭 _, by
        intro M sentence
        change (∀ p ∈ [sentence], p.Holds M) ↔ sentence.Holds M
        simp only [List.mem_singleton, forall_eq]⟩
      naturality := by
        intro A B f
        exact Room.hom_ext (by funext sentence; rfl) rfl }

/-- The original script receipt includes its entire declaration preamble,
command forms and every assertion, not just a single expression's bytes. -/
structure Family (A : Signature) where
  accepted : Quantified.Script.Accepted
  interpretation : localSignature accepted.checked ⟶ A

namespace Family
variable {A B C : Signature}

/-- Direct source interpretation of every original assertion in one actual
ambient-model reduct. This definition never evaluates a decoded typed term. -/
def Holds (M : Model A.symbols) (s : Family A) : Prop :=
  ∀ expression ∈ s.accepted.layout.assertions,
    Quantified.SExpr.Surface.Holds s.accepted.checked.environment
      (Hom.reduct s.interpretation M) expression

def map (f : A ⟶ B) (s : Family A) : Family B :=
  ⟨s.accepted, s.interpretation ≫ f⟩

@[simp] theorem map_accepted (f : A ⟶ B) (s : Family A) :
    (s.map f).accepted = s.accepted := rfl

@[simp] theorem map_text (f : A ⟶ B) (s : Family A) :
    (s.map f).accepted.text = s.accepted.text := rfl

@[simp] theorem map_id (s : Family A) : s.map (𝟙 A) = s := by
  cases s
  simp only [map, Category.comp_id]

@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (s : Family A) :
    s.map (f ≫ g) = (s.map f).map g := by
  change Family.mk s.accepted (s.interpretation ≫ (f ≫ g)) =
    Family.mk s.accepted ((s.interpretation ≫ f) ≫ g)
  rw [Category.assoc]

theorem holds_map (f : A ⟶ B) (M : Model B.symbols) (s : Family A) :
    (s.map f).Holds M ↔ s.Holds (Hom.reduct f M) := by
  unfold Holds map
  rw [Hom.model_reduct_comp]

/-- Decode every accepted assertion and transport it through the actual map. -/
def decode (s : Family A) : Problem A :=
  List.map (Hom.quantifiedSentence s.interpretation)
    (List.map (·.sentence) s.accepted.assertions)

@[simp] theorem decode_length (s : Family A) :
    s.decode.length = s.accepted.assertions.length := by
  simp only [decode, List.length_map]

theorem decode_holds (M : Model A.symbols) (s : Family A) :
    Problem.Holds M s.decode ↔ s.Holds M := by
  unfold Problem.Holds decode Holds
  simp only [List.forall_mem_map, Hom.holds_quantifiedSentence]
  simpa only [Quantified.Script.FixedHolds, List.forall_mem_map] using
    (Quantified.Script.fixed_holds_iff s.accepted
      (Hom.reduct s.interpretation M)).symm

theorem decode_map (f : A ⟶ B) (s : Family A) :
    (s.map f).decode = Problem.map f s.decode := by
  simp only [decode, map, Problem.map, List.map_map]
  congr 1
  funext assertion
  exact Hom.quantifiedSentence_comp s.interpretation f assertion.sentence

/-- Reuse a complete accepted script at its own checked local signature. -/
def ofAccepted (s : Quantified.Script.Accepted) : Family (localSignature s.checked) :=
  ⟨s, 𝟙 _⟩
end Family

/-- All ordinary operation-preserving model homomorphisms remain present. -/
def room (A : Signature) : Room.{0,0,1} :=
  ⟨Family A, Cat.of (Model A.symbols), Family.Holds⟩

def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨Family.map f, Hom.reductFunctor f, Family.holds_map f⟩

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext Family.map_id) (Hom.model_reductFunctor_id A)
  map_comp f g := Room.hom_ext (funext (Family.map_comp f g))
    (Hom.model_reductFunctor_comp f g)

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

/-- Exact decoder comparison with identity functors on the entire model category. -/
def toProblems : Inst.CoHom inst Problem.inst where
  Φ := 𝟭 _
  ρ :=
    { app A := ⟨Family.decode, 𝟭 _, Family.decode_holds⟩
      naturality := by
        intro A B f
        exact Room.hom_ext (funext (Family.decode_map f)) rfl }

end Silmaril.Logic.Smt.Uflia.SortMaps.Source.Script
