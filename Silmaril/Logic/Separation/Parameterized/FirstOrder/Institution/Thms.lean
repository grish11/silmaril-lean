module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Institution.Defs
public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Transport.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {A B : Signature}

def sentenceValues (A : Signature) (k : Nat) :
    Fin k → TargetTerm A (pointerHeapTargetSorts k) .value := fun i => .var i.succ

def sentenceHeap (A : Signature) (k : Nat) :
    TargetTerm A (pointerHeapTargetSorts k) .heap := .var 0

def sentence (p : Parameterized.Sentence A) : Canonical.Sentence A :=
  ⟨p.contextSize+1,fun i => profile A (p.profiles i),pointerHeapTargetSorts p.contextSize,
    pattern p.pre (sentenceValues A p.contextSize) (sentenceHeap A p.contextSize),
    pattern p.post (sentenceValues A p.contextSize) (sentenceHeap A p.contextSize)⟩

theorem sentence_satisfaction (M : Model A) (p : Parameterized.Sentence A) :
    Canonical.Sentence.Satisfies M (sentence p) ↔ p.Satisfies M := by
  have he : encodeRelEnv M (P := p.profiles) (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  constructor
  · intro hc s hs
    have hp := pattern_correct M p.pre (fun i => i.elim0)
      (sentenceValues A p.contextSize) (sentenceHeap A p.contextSize) (encodeState M s)
    have hq := pattern_correct M p.post (fun i => i.elim0)
      (sentenceValues A p.contextSize) (sentenceHeap A p.contextSize) (encodeState M s)
    rw [he] at hp hq
    exact hq.mp (hc (hp.mpr hs))
  · intro hs θ hp
    have hpre := pattern_correct M p.pre (fun i => i.elim0)
      (sentenceValues A p.contextSize) (sentenceHeap A p.contextSize) θ
    have hpost := pattern_correct M p.post (fun i => i.elim0)
      (sentenceValues A p.contextSize) (sentenceHeap A p.contextSize) θ
    rw [he] at hpre hpost
    exact hpost.mpr (hs (hpre.mp hp))

theorem sentence_map (f : A ⟶ B) (p : Parameterized.Sentence A) :
    Canonical.Sentence.map f (sentence p) = sentence (p.map f) := by
  cases p with
  | mk k P pre post =>
    exact congrArg₂ (fun a b => (⟨k+1,fun i => profile B (P i),pointerHeapTargetSorts k,a,b⟩ : Canonical.Sentence B))
      (pattern_map f pre (sentenceValues A k) (sentenceHeap A k))
      (pattern_map f post (sentenceValues A k) (sentenceHeap A k))

def comparison : Parameterized.institution ⟶ (𝟭 Signature) ⋙ Canonical.institution where
  app A := ⟨sentence,𝟭 (Model A),sentence_satisfaction⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      exact (sentence_map f p).symm
    · rfl

/-- A genuine institution comorphism, retaining every actual source model
homomorphism. Its target sentences are arbitrary native formula pairs. -/
def toCanonical : Inst.CoHom Parameterized.inst Canonical.inst := ⟨𝟭 _,comparison⟩

theorem toCanonical_modelExpansive : toCanonical.ModelExpansive :=
  fun _ M => ⟨M,rfl⟩

theorem sat_iff (p : Parameterized.Sentence A) :
    (∃ M : Model A, p.Satisfies M) ↔ ∃ M : Model A, Canonical.Sentence.Satisfies M (sentence p) := by
  constructor
  · rintro ⟨M,h⟩
    exact ⟨M,(sentence_satisfaction M p).mpr h⟩
  · rintro ⟨M,h⟩
    exact ⟨M,(sentence_satisfaction M p).mp h⟩

theorem unsat_iff (p : Parameterized.Sentence A) :
    (¬ ∃ M : Model A, p.Satisfies M) ↔ ¬ ∃ M : Model A, Canonical.Sentence.Satisfies M (sentence p) :=
  not_congr (sat_iff p)

theorem entails_iff (H : Set (Parameterized.Sentence A)) (p : Parameterized.Sentence A) :
    (Parameterized.institution.obj A).Entails H p ↔
      (Canonical.institution.obj A).Entails (sentence '' H) (sentence p) :=
  toCanonical.entails_iff toCanonical_modelExpansive A H p

end Silmaril.Logic.Separation.Parameterized.FirstOrder
