module
public import Silmaril.X86.SystemV.Defs
public import Silmaril.Project.Shapes.SysV.Rtl.Defs

/-! The Boolean boundary accepts unspecified upper register bits, but rejects
noncanonical low-byte values. This is ABI coverage, not a corpus refinement. -/
open Silmaril.X86.SystemV

example : Encodes .boolean true (BitVec.ofNat 64 0xabcdef01) := by unfold Encodes; decide +kernel
example : Encodes .boolean false (BitVec.ofNat 64 0xabcdef00) := by unfold Encodes; decide +kernel
example : ¬ Encodes .boolean true (BitVec.ofNat 64 0) := by unfold Encodes; decide +kernel
example : ¬ Encodes .boolean false (BitVec.ofNat 64 1) := by unfold Encodes; decide +kernel
example : ¬ Encodes .boolean true (BitVec.ofNat 64 3) := by unfold Encodes; decide +kernel
example : ¬ Encodes .boolean false (BitVec.ofNat 64 2) := by unfold Encodes; decide +kernel
example : ¬ Encodes .boolean true (BitVec.ofNat 64 0x181) := by unfold Encodes; decide +kernel

example : CApi.Scalar.signed .boolean true = 1 := by rfl
example : CApi.Scalar.signed .boolean false = 0 := by rfl
example : Silmaril.Project.Shapes.SysV.argWord .boolean true = BitVec.ofNat 64 1 := by rfl
example : Silmaril.Project.Shapes.SysV.argWord .boolean false = BitVec.ofNat 64 0 := by rfl
