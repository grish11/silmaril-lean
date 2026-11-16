module

public import Silmaril.Logic.Temporal.CTLStar.Compiler.Institution.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler.Institution.Examples
open CategoryTheory

def sig : CTLStar.Signature := ⟨Bool⟩
def oneSig : CTLStar.Signature := ⟨Unit⟩
def collapse : sig ⟶ oneSig := fun _ => ()

def leftModel : CTLStar.Model sig :=
  ⟨⟨Bool, fun _ _ => False, fun _ _ => True, false⟩⟩
def rightModel : CTLStar.Model sig :=
  ⟨⟨Bool, fun _ _ => False, fun _ _ => True, true⟩⟩

/-- A genuine world permutation between differently pointed source models. -/
def swapFrame : CTLStar.FrameIso leftModel rightModel where
  equiv := ⟨Bool.not, Bool.not, by intro b; cases b <;> rfl,
    by intro b; cases b <;> rfl⟩
  point := rfl
  atoms _ _ := Iff.rfl
  edges _ _ := Iff.rfl

def swapArrow : (⟨leftModel.toModal⟩ : CTLStar.RichModel sig) ⟶
    (⟨rightModel.toModal⟩ : CTLStar.RichModel sig) := ⟨swapFrame.toModalIso⟩

theorem swap_moves_world : swapArrow.iso.hom.map false = true := rfl

theorem pointed_models_differ : leftModel ≠ rightModel := by
  intro h
  cases h

/-- Rich source arrows remain present; translation respects their satisfaction. -/
theorem swap_compiled_sat (p : StateFormula sig) :
    ModalMu.Sat (encodeModel leftModel) (compileState p) ↔
      ModalMu.Sat (encodeModel rightModel) (compileState p) := by
  exact (compileState_correct p leftModel ModalMu.emptyEnv false).trans
    ((CTLStar.rich_hom_sat swapArrow p).trans
      (compileState_correct p rightModel ModalMu.emptyEnv true).symm)

def incompatibleAtoms : StateFormula sig := .conj (.atom false) (.neg (.atom true))

theorem collapse_syntax :
    (compileState incompatibleAtoms).map (toMuMap collapse) =
      compileState (incompatibleAtoms.map collapse) := compileState_map _ _

theorem collapsed_rejects (N : ModalMu.Model (toMuSig oneSig)) :
    ¬ ModalMu.Sat N (compileState (incompatibleAtoms.map collapse)) := by
  rw [compile_sat]
  change ¬ ((decodeModel N).toModal.valuation () (decodeModel N).toModal.point ∧
    ¬ (decodeModel N).toModal.valuation () (decodeModel N).toModal.point)
  tauto

end Silmaril.Logic.Temporal.CTLStar.Compiler.Institution.Examples
