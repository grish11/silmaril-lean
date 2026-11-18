module

public import Silmaril.Compiler.Explorer.Decompiled.Defs

/-!
# Decompiled blocks: theorems

`decompiledBlock_of`: the computable facts (the proposal, the checker's acceptance, the lowering
and the printing) give `DecompiledBlock`, through `WordC.checked_output_c0`. An instance needs
only those facts, each decidable by evaluation.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

open Silmaril.X86 (Word Reg MState Byte)
open Silmaril.X86.Decompile.SemLift
open Silmaril.Compiler.Decompile.WordC

/-- **The decompiler's facts give the obligation.** -/
theorem decompiledBlock_of {name : String} {code : List Byte} {n : Nat}
    {inputs : List (Reg × String)} {source : String} {summary : Summary} {expr : Ex}
    {term : Silmaril.Cerberus.Assertion.Pure.Term}
    (hp : propose code n [.rax] = some summary) (hc : check code n summary = true)
    (ho : (Reg.rax, expr) ∈ summary.outs)
    (hl : fromSSA (fun r => inputs.lookup r) expr = .ok term)
    (hs : printFunction name (inputs.map Prod.snd) term = .ok source) :
    DecompiledBlock name code n inputs source :=
  ⟨summary, expr, term, hp, hc, ho, hl, hs, fun exit base initial pre values hv symbols program
    function env locals =>
    checked_output_c0 exit base code n summary hc initial pre .rax expr ho
      (fun r => inputs.lookup r) values hv hl symbols program function env locals⟩

end Silmaril.Compiler.Explorer

end
