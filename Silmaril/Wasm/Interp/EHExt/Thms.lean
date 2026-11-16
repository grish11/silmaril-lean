module

public import Silmaril.Wasm.Interp.EHExt.Defs
public import Silmaril.Proofs.Wasm.Interp.EHExt

/-!
# The arity checker extension with exceptions: theorems

* `ehExt_of_not_eh`: off `throw`, `throw_ref` and `try_table`, `ehExt tags` is `tExt`;
* `chkE_ehExt_of_tExt`, `storeChkE_ehExt_of_tExt`: every `tExt`-checked tree (store) is
  `ehExt`-checked with the same result, so the exception checker only adds code;
* `tagFields_of_tag?`: the field count `ehExt` reads for `throw x` is the one Core's `throw` pops.

The Core adequacy of the exception rules (`CallXE.EvalOXE`) under this checker is the next step.
-/

public section

namespace Silmaril.Wasm.Interp.EHExt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

variable {H : Type}

theorem ehExt_of_not_eh {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {i : Instr} (h₁ : ∀ x, i ≠ .throw x) (h₂ : i ≠ .throwRef)
    (h₃ : ∀ bt cs b, i ≠ .tryTable bt cs b) : ehExt tags F mi i = tExt F mi i :=
  Silmaril.Wasm.Interp.ehExt_of_not_eh h₁ h₂ h₃

theorem chkE_ehExt_of_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} (oh : Option Nat) (es : List Binaryen.BExpr) {o : Option Nat}
    (hc : chkE tExt F mi nl ret labels oh es = some o) :
    chkE (ehExt tags) F mi nl ret labels oh es = some o :=
  Silmaril.Wasm.Interp.chkE_ehExt_of_tExt oh es hc

theorem storeChkE_ehExt_of_tExt {tags : List TagInst} {F : List (FuncInst H)}
    (hS : StoreChkE tExt F) : StoreChkE (ehExt tags) F :=
  Silmaril.Wasm.Interp.storeChkE_ehExt_of_tExt hS

theorem tagFields_of_tag? {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Validation.Ty (.list .val)} (ht : s.tag? f x = some (ta, ti))
    (he : Validation.Expand ti.type (.func ts .nil)) :
    tagFields s.tags f.module x = some ts.length :=
  Silmaril.Wasm.Interp.tagFields_of_tag? ht he

end Silmaril.Wasm.Interp.EHExt
