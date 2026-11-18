module

public import Silmaril.Compiler.Explorer.Decompiled.Thms
-- The printing's string operations unfold only with their bodies (as in the generated
-- canonical-safety proofs of `examples/compiles-to`).
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Repr

/-!
# The decompiled fixture as an obligation

`examples/compiler-explorer/decompile/`: gcc 13.3.0 `-O2` compiled `scale.c` to `scale.o`, whose
`.text` starts with the block `lea -0x5(%rsi,%rdi,8),%rax` (the five bytes below) before `ret`;
the decompiler printed `scale.dec.c`. `scale` instantiates `DecompiledBlock` for exactly those
bytes and that text: the facts are checked by the kernel's evaluation (`decide +kernel`, `rfl`).
That the bytes are the object's is checked by the explorer's database against the ELF file (not
by the kernel); that the text is `scale.dec.c` is checked by the database against the artifact.
-/

@[expose] public section

namespace CompilesToExamples.Explorer.Decompiled

open Silmaril.Compiler.Explorer Silmaril.X86.Decompile.SemLift Silmaril.Compiler.Decompile.WordC

/-- The block's bytes (`.text [0x0, 0x5)` of `scale.o`). -/
abbrev bytes : List Silmaril.X86.Byte := [0x48, 0x8d, 0x44, 0xfe, 0xfb]

/-- The decompiler's output, `scale.dec.c`. -/
abbrev source : String :=
  "unsigned long long wc_scale(unsigned long long wc_a, unsigned long long wc_b) {\n  return ((wc_b + (wc_a * 8ULL)) + 18446744073709551611ULL);\n}\n"

/-- The summary the proposer computes. -/
def summary : Summary := (propose bytes 1 [.rax]).getD ⟨[], [], [], 0, .unknown, []⟩

/-- The `rax` expression, lowered. -/
def term : Silmaril.Cerberus.Assertion.Pure.Term :=
  ((fromSSA (fun r => [(Silmaril.X86.Reg.rdi, "a"), (.rsi, "b")].lookup r)
    (summary.outs.headD (.rax, .const 0)).2).toOption.getD (.literal 0))

set_option maxRecDepth 4096 in
/-- **The decompiled block**: checked summary, the printed text, and machine-to-C0 agreement. -/
theorem scale : DecompiledBlock "scale" bytes 1 [(.rdi, "a"), (.rsi, "b")] source := by
  refine decompiledBlock_of (summary := summary) (expr := (summary.outs.headD (.rax, .const 0)).2)
    (term := term) ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide +kernel
  · exact List.mem_cons_self
  · rfl
  · show printFunction "scale" ["a", "b"] term = .ok source
    rfl

end CompilesToExamples.Explorer.Decompiled

end
