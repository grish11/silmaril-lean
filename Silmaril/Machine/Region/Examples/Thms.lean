module

public import Silmaril.Machine.Region.Examples.Defs
import Silmaril.Proofs.Machine.Region.Examples

@[expose] public section
namespace Silmaril.Machine.Region.Examples
open Silmaril.Semantics.Region

theorem jump_sound : Sound (X86.system 0xffff) jumpAdmit jumpSupport (fun l => l = 2) :=
  Proofs.jump_sound

/-- Nonvacuous, semantically certified direct branch from loaded bytes. -/
theorem jump_valid : Valid (X86.system 0xffff) (fun l => l < 2 ^ 64)
    jumpAdmit jumpSupport 0 {2} := Proofs.jump_valid

theorem classification_report : classificationReport = (7, 7, 5) := by decide +kernel
theorem truncated_branch : (Silmaril.X86.Decompile.Region.mk 0 [0xeb]).decode? 10 = none := by
  decide +kernel
theorem unsupported_opcode : (Silmaril.X86.Decompile.Region.mk 0 [0xff]).decode? 10 = none := by
  decide +kernel
theorem ambiguous_mapping : translate [mapping, mapping] ⟨.virtual, 0x1000⟩ = none := by
  decide +kernel
theorem virtual_mapping : translate [mapping] ⟨.virtual, 0x1001⟩ = some 0x41 := by
  decide +kernel
theorem section_is_not_virtual : translate [mapping] ⟨.section 0, 0x1001⟩ = none := by
  decide +kernel
end Silmaril.Machine.Region.Examples
