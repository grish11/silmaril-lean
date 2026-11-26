module

import Silmaril.SSA.Isotope.Institution.Relational.Thms

/-! Public-header regressions for native sequential satisfaction and relabelling. -/

namespace Silmaril.Isotope.Institution.Relational.Tests

open CategoryTheory Semantics Theory
open Silmaril.Logic.Institution (modelFunctor sentenceFunctor)

abbrev Sorts := Ty Unit

def bit : Sorts := .base ()
abbrev D : Sorts → Type := Ty.denote (fun _ => Bool)


inductive Op where
  | copy | flip | yes | step | otherStep

def Op.result : Op → Sorts
  | .copy | .flip | .yes => bit
  | .step | .otherStep => .coprod bit bit

def S : InstrSig Sorts Unit where
  Instr := Op
  hasTy := ⟨fun _ => bit, Op.result⟩
  hasEff := ⟨fun _ => ()⟩

def swap : S ⟶ S where
  instr
    | .copy => .flip
    | .flip => .copy
    | .yes => .yes
    | .step => .otherStep
    | .otherStep => .step
  source _ := rfl
  target f := by cases f <;> rfl
  effect _ := rfl

theorem swap_nonidentity : swap ≠ 𝟙 S := by
  intro h
  have hop := congrArg (fun g : S ⟶ S => g.instr Op.copy) h
  cases hop

theorem swap_twice : swap ≫ swap = 𝟙 S :=
  InstrSig.Hom.ext (funext fun op => by cases op <;> rfl)

def CopySignature : InstrSig Sorts Unit where
  Instr := Unit
  hasTy := ⟨fun _ => bit, fun _ => bit⟩
  hasEff := ⟨fun _ => ()⟩

def includeCopy : CopySignature ⟶ S :=
  ⟨fun _ => Op.copy, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def feedback (result : Bool) (state : Bool) : Bool ⊕ Bool :=
  if state then .inl result else .inr true

def M : Model D S where
  eval
    | .copy, a, b => b = a
    | .flip, a, b => b = !(a : Bool)
    | .yes, _, b => b = true
    | .step, a, b => b = feedback true a
    | .otherStep, a, b => b = feedback false a

def allResults : Model D S := ⟨fun _ _ _ => True⟩

def inclusion : M ⟶ allResults := ⟨fun _ _ _ _ => trivial⟩

theorem reduct_changes_primitive : (M.reduct swap).eval Op.copy false true ∧
    ¬ M.eval Op.copy false true :=
  ⟨rfl, Bool.noConfusion⟩

theorem inclusion_reduct :
    (M.reduct includeCopy).eval () false false ∧
      (M.reduct (includeCopy ≫ swap)).eval () false true :=
  ⟨rfl, rfl⟩

theorem composed_reduct :
    M.reduct (includeCopy ≫ swap) = (M.reduct swap).reduct includeCopy :=
  Model.reduct_comp includeCopy swap M

def reduct_arrow :
    (Model.reductFunctor D swap).obj M ⟶ (Model.reductFunctor D swap).obj allResults :=
  (Model.reductFunctor D swap).map inclusion

theorem reduct_inclusion_strict :
    ¬ Nonempty ((Model.reductFunctor D swap).obj allResults ⟶
      (Model.reductFunctor D swap).obj M) := by
  rintro ⟨h⟩
  exact Bool.noConfusion (h.down Op.copy false false trivial)

def Γ : Ctx Empty Sorts := .nil
def freeEnv : FreeEnv D Γ := fun x => nomatch x
def slot (A : Sorts) : BoundCtx Sorts 1 := .snoc .nil A
def env {A : Sorts} (a : D A) : BoundEnv D (slot A) :=
  BoundEnv.snoc (fun i => Fin.elim0 i) a

def seqEquation : LetSeq.Sentence S Γ :=
  ⟨⟨1, slot bit, bit⟩,
    ⟨.let₁ (.op Op.copy (.bv 0)) (.bv 0), .let₁ (.op .bv) .bv⟩,
    ⟨.bv 0, .bv⟩⟩

theorem seq_true : LetSeq.Sentence.Satisfies M seqEquation := by
  intro γ ρ b
  change (∃ a, (∃ x, x = ρ (0 : Fin 1) ∧ a = x) ∧ b = a) ↔ b = ρ (0 : Fin 1)
  simp

theorem seq_false_in_reduct : ¬ LetSeq.Sentence.Satisfies (M.reduct swap) seqEquation := by
  intro h
  have hb := h freeEnv (env (A := bit) false) true
  change (∃ a : Bool, (∃ x : Bool, x = false ∧ a = !x) ∧ true = a) ↔ true = false at hb
  exact Bool.noConfusion (hb.mp ⟨true, ⟨false, rfl, rfl⟩, rfl⟩)

theorem seq_translated_false : ¬ LetSeq.Sentence.Satisfies M
    ((sentenceFunctor (LetSeq.institution (ε := Unit) D Γ)).map swap seqEquation) :=
  fun h => seq_false_in_reduct ((LetSeq.Sentence.satisfaction swap M seqEquation).mp h)

def caseEquation : LetCase.Sentence S Γ :=
  ⟨⟨1, slot (.coprod bit bit), bit⟩,
    ⟨.case (.bv 0) (.op Op.copy (.bv 0)) (.bv 0), .case .bv (.op .bv) .bv⟩,
    ⟨.case (.bv 0) (.bv 0) (.bv 0), .case .bv .bv .bv⟩⟩

theorem case_true : LetCase.Sentence.Satisfies M caseEquation := by
  intro γ ρ b
  dsimp [caseEquation, LetCase.LocallyNameless.Derivation.denoteRelation, M]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  cases CoproductModel.coprodEquiv (D := D) bit bit e with
  | inl a =>
      change (∃ x : Bool, x = a ∧ b = x) ↔ b = a
      exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨a, rfl, h⟩⟩
  | inr _ => rfl

theorem case_false_in_reduct : ¬ LetCase.Sentence.Satisfies (M.reduct swap) caseEquation := by
  intro h
  have hb := h freeEnv (env (A := .coprod bit bit) (.inl false)) true
  dsimp [caseEquation, LetCase.LocallyNameless.Derivation.denoteRelation] at hb
  obtain ⟨e, he, hout⟩ := hb.mp ⟨Sum.inl false, rfl, false, rfl, rfl⟩
  change e = Sum.inl false at he
  subst e
  exact Bool.noConfusion hout

theorem case_translated_false : ¬ LetCase.Sentence.Satisfies M
    (((Silmaril.Isotope.Institution.LetCase.inst (ε := Unit) Γ).map swap).sen caseEquation) :=
  fun h => case_false_in_reduct ((LetCase.Sentence.satisfaction swap M caseEquation).mp h)

def iterEquation : LetIter.Sentence S Γ :=
  ⟨⟨1, slot bit, bit⟩,
    ⟨.iter (.bv 0) (.op Op.step (.bv 0)), .iter .bv (.op .bv)⟩,
    ⟨.op Op.yes (.bv 0), .op .bv⟩⟩

theorem step_returns_true {a b : Bool} (run :
    Relation.Iterates (fun s r => r = feedback true s) a b) :
    b = true := by
  induction run with
  | @done s b h => cases s <;> simp_all [feedback]
  | more _ _ ih => exact ih

theorem iter_true : LetIter.Sentence.Satisfies M iterEquation := by
  intro γ ρ b
  let step : Bool → Bool ⊕ Bool → Prop :=
    fun s r => r = feedback true s
  change (∃ a : Bool, a = ρ (0 : Fin 1) ∧
    Relation.Iterates (fun s r => ∃ x : Bool, x = s ∧ step x r) a b) ↔
    (∃ x : Bool, x = ρ (0 : Fin 1) ∧ b = true)
  have hs (s : Bool) (r : Bool ⊕ Bool) : (∃ x : Bool, x = s ∧ step x r) ↔ step s r := by simp
  simp only [hs]
  constructor
  · rintro ⟨_, _, run⟩
    exact ⟨ρ (0 : Fin 1), rfl, step_returns_true run⟩
  · rintro ⟨_, _, rfl⟩
    have reaches (a : Bool) : Relation.Iterates step a true := by
      cases a with
      | false => exact .more (a' := true) rfl (.done rfl)
      | true => exact .done rfl
    exact ⟨ρ (0 : Fin 1), rfl, reaches _⟩

theorem iter_false_in_reduct : ¬ LetIter.Sentence.Satisfies (M.reduct swap) iterEquation := by
  intro h
  have hb := h freeEnv (env (A := bit) false) false
  change (∃ a : Bool, a = false ∧ Relation.Iterates
    (fun s r => ∃ x : Bool, x = s ∧ r = feedback false x) a false) ↔
    (∃ x : Bool, x = false ∧ false = true) at hb
  have run : Relation.Iterates
      (fun s r => ∃ x : Bool, x = s ∧ r = feedback false x)
      false false :=
    .more (a' := true) ⟨false, rfl, rfl⟩ (.done ⟨true, rfl, rfl⟩)
  obtain ⟨_, _, hfalse⟩ := hb.mp ⟨false, rfl, run⟩
  exact Bool.noConfusion hfalse

theorem iter_translated_false : ¬ LetIter.Sentence.Satisfies M
    ((sentenceFunctor (LetIter.institution (ε := Unit) D Γ)).map swap iterEquation) :=
  fun h => iter_false_in_reduct ((LetIter.Sentence.satisfaction swap M iterEquation).mp h)

theorem iter_reduct_projection :
    ((modelFunctor (LetIter.institution (ε := Unit) D Γ)).map swap.op).toFunctor.obj M =
      M.reduct swap := rfl

-- The composite preserves truth and carries the selected witnesses through a swap.
theorem seq_iter_true :
    LetIter.Sentence.Satisfies M (caseIterSentence (seqCaseSentence seqEquation)) :=
  ((seqIterCoHom (ε := Unit) Γ D).satisfaction S M seqEquation).mpr seq_true

theorem seq_iter_translated_false :
    ¬ LetIter.Sentence.Satisfies M
      (LetIter.Sentence.translate swap (caseIterSentence (seqCaseSentence seqEquation))) := by
  rw [← seqIterSentence_natural]
  exact fun h => seq_translated_false ((seqIter_satisfaction M _).mp h)

-- The second inclusion also exercises a native branch and the reduct on model arrows.
theorem case_iter_true : LetIter.Sentence.Satisfies M (caseIterSentence caseEquation) :=
  (caseIter_satisfaction M caseEquation).mpr case_true

theorem case_iter_false_in_reduct :
    ¬ LetIter.Sentence.Satisfies (M.reduct swap) (caseIterSentence caseEquation) :=
  fun h => case_false_in_reduct ((caseIter_satisfaction _ _).mp h)

example :
    (((caseIterRho Γ D).app S).mod ⋙ Model.reductFunctor D swap).map inclusion =
      (Model.reductFunctor D swap ⋙ ((caseIterRho Γ D).app S).mod).map inclusion := rfl

end Silmaril.Isotope.Institution.Relational.Tests
