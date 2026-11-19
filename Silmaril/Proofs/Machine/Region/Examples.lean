module

public import Silmaril.Machine.Region.Examples.Defs

@[expose] public section
namespace Silmaril.Machine.Region.Examples.Proofs
open Silmaril.Semantics.Region
open Silmaril.X86.Decompile

theorem jump_sound : Sound (X86.system 0xffff) jumpAdmit jumpSupport (fun l => l = 2) := by
  apply X86.listing_sound (ds := [jumpInstruction]) (fuel := 1) (r := jump) (D := jumpAdmit)
    (ret := 0xffff) (U := jumpSupport) (X := fun l => l = 2)
    (by decide +kernel) (fun _ h => h)
  · intro s hs _
    exact ⟨hs.2, jumpInstruction, by simp, hs.1⟩
  · intro s es t hs hu step ht
    have allows := X86.listing_step (r := jump) (fuel := 1) (ds := [jumpInstruction]) (d := jumpInstruction)
      (by decide +kernel) hs.2 (by simp) hs.1 (show (X86.system 0xffff).step s [] t from ⟨rfl, step.2⟩)
    have rip : t.core.rip.toNat = 2 := by
      have targets : X86.instructionTargets jumpInstruction = .finite {2} := rfl
      rw [targets] at allows
      exact Finset.mem_singleton.mp allows
    exact False.elim ((by decide : (2 : Nat) ≠ 0) (rip.symm.trans ht))
  · intro d hd l hl _
    have hd' : d = jumpInstruction := List.mem_singleton.mp hd
    subst d
    have targets : X86.instructionTargets jumpInstruction = .finite {2} := rfl
    rw [targets] at hl
    exact Finset.mem_singleton.mp hl

theorem jump_valid : Valid (X86.system 0xffff) (fun l => l < 2 ^ 64)
    jumpAdmit jumpSupport 0 {2} := by
  refine ⟨by decide, rfl, ⟨initial, rfl, ?_⟩, fun _ h => h.1, ?_, ?_⟩
  · exact Silmaril.X86.Decompile.Region.loadedIn_load jump (by decide)
  · intro l hl
    have : l = 2 := Finset.mem_singleton.mp hl
    subst l
    decide
  · exact fun s es t ha hf => Finset.mem_singleton.mpr (jump_sound s es t ha hf)

end Silmaril.Machine.Region.Examples.Proofs
