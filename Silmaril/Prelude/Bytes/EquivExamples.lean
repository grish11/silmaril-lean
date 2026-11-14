module

public import Silmaril.Prelude.Bytes.Equiv.Thms
public import Silmaril.Prelude.Bytes.WriteExamples

/-! # Kernel bytes up to their bytes: examples on `hello-gcc`

`≈` relates differently shaped trees of the same file: a rope of two slices, its canonical
form and the two writes. The facts that need evaluation are checked by the kernel.
-/

@[expose] public section

namespace Silmaril.KBytes.EquivExamples

open Silmaril.KBytes Silmaril.KBytes.KernelExamples Silmaril.KBytes.WriteExamples

/-- The rope of two unaligned slices holds the file's bytes. -/
theorem rope_equiv : rope ≈ hello := rope_toList

/-- Path copying and the rope give equivalent trees after the same cross-leaf write. -/
theorem crossed_equiv : hello.ropeWrite 4092 8 0x1122334455667788 ≈ crossed :=
  ropeWrite_equiv_write hello.wf_true _ (hello_len_le (by decide))

/-- Canonical forms compare structurally: the kernel decides `≈` by `beq`. -/
theorem crossed_canon_equiv : hello.ropeWrite 4092 8 0x1122334455667788 ≈ crossed :=
  equiv_of_canon_beq 4096
    (wf_ropeWrite _ _ _ _ hello.wf_true (hello_len_le (by decide)))
    (wf_write _ _ _ _ hello.wf_true (hello_len_le (by decide)))
    (by decide +kernel)

/-- Writing the same field of equivalent trees gives equivalent trees. -/
theorem rope_write_equiv : rope.write 24 8 0x401000 ≈ entryA :=
  write_congr (wf_append (wf_slice _ _ _ hello.wf_true (hello_len_le (by decide)))
      (wf_slice _ _ _ hello.wf_true (hello_len_le (by decide))))
    hello.wf_true rope_equiv _ (by decide +kernel)

end Silmaril.KBytes.EquivExamples
