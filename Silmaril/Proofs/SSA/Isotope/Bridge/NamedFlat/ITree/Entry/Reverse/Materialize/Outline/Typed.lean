module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
open LambdaSSA (FiniteCFG Flat)
open SSA.FiniteSum (append append_left append_right)
open LetCase.LocallyNameless (HasType)

universe u v
variable {τ : Type u} [TypeFormers τ] {F : Type v} [HasTy F τ]
  {labels newLabels blocks exits n : Nat} {β : BoundCtx τ n}
  {R : Fin blocks → τ} {D : Fin exits → τ} {g : FiniteCFG F blocks exits n}

private theorem rename_hasType {L : Fin labels → τ} {M : Fin newLabels → τ} {t : Flat F labels n}
    (typed : t.HasType L β) (ρ : Fin labels → Fin newLabels) (agree : ∀ i, M (ρ i) = L i) :
    (renameLabels ρ t).HasType M β := by
  induction typed with
  | br ha => exact .br (agree _ ▸ ha)
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ left right => exact .case ha left right

theorem type_relocate (i : Fin blocks) (left : τ) (j : Fin (blocks + exits)) :
    append (packets R i left) D (relocate blocks exits j) = append R D j := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [relocate, packets]
  · simp [relocate]

theorem selection_typed (s : Selection g) (typed : g.HasType β R D) :
    ∃ left right, s.arm.HasType β (append R D) (R s.selected) left right := by
  have row := typed.block s.selected
  rw [s.readback] at row
  cases row with
  | case hd hl hr =>
    cases hl with
    | br ha => exact ⟨_, _, ⟨hd, ha, hr⟩⟩

theorem graph_hasType (s : Selection g) (typed : g.HasType β R D) {left right : τ}
    (arm : s.arm.HasType β (append R D) (R s.selected) left right) :
    (graph s).HasType β (packets R s.selected left) D := by
  let agree := type_relocate (R := R) (D := D) s.selected left
  refine ⟨rename_hasType typed.entry _ agree, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [graph, Fin.lastCases_last, packets] using
      (show s.arm.continuation.HasType (append (packets R s.selected left) D)
        (β.snoc (product (R s.selected) left)) from
        Flat.HasType.let₂ .bv (.br (agree _ ▸ arm.active.underTwoBinders (X := product (R s.selected) left))))
  · by_cases selected : j = s.selected
    · subst j
      simp only [graph, Fin.lastCases_castSucc, packets, ↓reduceIte]
      apply Flat.HasType.case arm.discr _ (rename_hasType arm.bypass _ agree)
      apply Flat.HasType.br
      rw [append_left, packets, Fin.lastCases_last]
      exact .pair .bv .bv
    · simpa only [graph, Fin.lastCases_castSucc, packets, selected, ↓reduceIte] using
        rename_hasType (typed.block j) _ agree

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
