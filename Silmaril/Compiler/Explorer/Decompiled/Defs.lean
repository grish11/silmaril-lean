module

public import Silmaril.Compiler.Decompile.WordC.Thms

/-!
# Decompiled blocks as explorer obligations

The obligation a compiler explorer can state for a block decompiled by the repository's
decompiler (`Silmaril.X86.Decompile.SemLift` and `Silmaril.Compiler.Decompile.WordC`).

`DecompiledBlock name code n inputs source` says:

* the proposer's summary of the first `n` instructions of `code` (live-out `rax`) is accepted by
  the checker (`SemLift.check`, the function `SemLift.check_sound` is about);
* its `rax` expression lowers to a term (`WordC.fromSSA`) that prints as exactly `source`
  (`WordC.printFunction`): the decompiled C text is the printing of that term;
* (`WordC.checked_output_c0`) from every machine state where the block is loaded and entered,
  with values for the inputs read from their registers, the machine reaches a state whose `rax`
  is the value the C0 interpreter gives the term's typed Ail, in every C0 environment holding the
  inputs.

What it does not say: the C text is *printed from* the term; it is not parsed or elaborated
back, so nothing relates the text to Cerberus or C0 except that printing. The block stops before
any control transfer (the final `ret` is outside it), and C0 is the repository's C subset
interpreter, not Cerberus.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

open Silmaril.X86 (Word Reg MState Byte)
open Silmaril.X86.Decompile.SemLift
open Silmaril.Compiler.Decompile.WordC
open Silmaril.Compile.C.Sem

/-- **A decompiled block**: checked summary, the printed source, and the machine-to-C0 agreement
of `WordC.checked_output_c0` for the block's `rax`. -/
def DecompiledBlock (name : String) (code : List Byte) (n : Nat) (inputs : List (Reg × String))
    (source : String) : Prop :=
  ∃ summary expr term,
    propose code n [.rax] = some summary ∧ check code n summary = true ∧
    (Reg.rax, expr) ∈ summary.outs ∧
    fromSSA (fun r => inputs.lookup r) expr = .ok term ∧
    printFunction name (inputs.map Prod.snd) term = .ok source ∧
    ∀ (exit base : Word) (initial : MState),
      Silmaril.X86.Decompile.VC.BlockPre code base summary initial →
      ∀ values : String → Word, (∀ r v, inputs.lookup r = some v → values v = initial.core.read r) →
      ∀ symbols program function env, Locals symbols values env term →
        ∃ final, Silmaril.X86.Ext.Reaches exit initial final ∧
          C0.evalE program (height term) function (toAil symbols term) env =
            .ok ((final.core.read .rax).toNat, env)

end Silmaril.Compiler.Explorer

end
