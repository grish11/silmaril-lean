module

public import Silmaril.Wasm.Acceptor.Code.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs
import Silmaril.Proofs.Wasm.Acceptor.Code

/-!
# The acceptor kit: code and instance facts, and call rules

Proofs in `Silmaril.Proofs.Wasm.Acceptor.Code`. Every profile and host relation.

* **`ibeqs_sound`**: the Boolean code comparison is sound;
* **`fn_of_fnOk`**: one kernel check `(List.range n).all (fnOk S m mi tys) = true` gives, for
  each `j < n`, that function `j` of the store has the code of function `j` of the module, the
  module instance `mi` and the expanded type `tys[j]`;
* **`w_call`**, **`w_callVoid`**, **`w_callI32`**: `call j` of a function with a valid
  specification (`FSpecValid`) in the every-run logic; for a function returning nothing or one
  `i32`, the continuation only needs to hold from the stores the specification promises.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Numerics (Profile)

theorem ibeqs_sound (as bs : List Instr) (h : ibeqs as bs = true) : as = bs :=
  Silmaril.Proofs.Wasm.Acceptor.ibeqs_sound as bs h

/-- **The instance facts of one function**, from the kernel check of all of them. -/
theorem fn_of_fnOk {H : Type} {S : Store H} {m : Module} {mi : ModuleInst} {tys : List CCompType}
    {n : Nat} (h : (List.range n).all (fnOk S m mi tys) = true) {j : Nat} (hj : j < n) :
    ∃ (fi : FuncInst H) (f : Func) (ty : CCompType),
      S.funcs[j]? = some fi ∧ m.funcs[j]? = some f ∧ tys[j]? = some ty ∧
      fi.code = .wasm f ∧ fi.module = mi ∧ Expand fi.type ty :=
  Silmaril.Proofs.Wasm.Acceptor.fn_of_fnOk h hj

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {rest : List Admin}
  {Q : Post H}

/-- **`call j`** of a function with a valid specification. -/
theorem w_call {f : Frame} {j a : Nat} {fi : FuncInst H} {S : FSpec H} {vs₀ args : List Val}
    (hj : j < 2 ^ 32) (hx : f.module.funcs[j]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, callPost f vs₀ (S.post s args) s' f o → seqPost P host rest Q s' f o) :
    HWP P host s f (vals (vs₀ ++ args) ++ .plain (callf j) :: rest) Q :=
  Silmaril.Proofs.Wasm.Acceptor.w_call hj hx hf hS hpre hpost

/-- `call j` of a function that returns nothing, in a store satisfying `R`. -/
theorem w_callVoid {f : Frame} {j a : Nat} {fi : FuncInst H} {S : FSpec H} {vs₀ args : List Val}
    {R : Store H → Prop} (hj : j < 2 ^ 32) (hx : f.module.funcs[j]? = some a)
    (hf : s.funcs[a]? = some fi) (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal [] ∧ R s')
    (k : ∀ s', R s' → HWP P host s' f (vals vs₀ ++ rest) Q) :
    HWP P host s f (vals (vs₀ ++ args) ++ .plain (callf j) :: rest) Q :=
  Silmaril.Proofs.Wasm.Acceptor.w_callVoid hj hx hf hS hpre hpost k

/-- `call j` of a function that returns one `i32`, in a store satisfying `R` with it. -/
theorem w_callI32 {f : Frame} {j a : Nat} {fi : FuncInst H} {S : FSpec H} {vs₀ args : List Val}
    {R : Store H → BitVec 32 → Prop} (hj : j < 2 ^ 32) (hx : f.module.funcs[j]? = some a)
    (hf : s.funcs[a]? = some fi) (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → ∃ v : BitVec 32, o = .normal [Val.i32 v] ∧ R s' v)
    (k : ∀ s' v, R s' v → HWP P host s' f (vals (vs₀ ++ [Val.i32 v]) ++ rest) Q) :
    HWP P host s f (vals (vs₀ ++ args) ++ .plain (callf j) :: rest) Q :=
  Silmaril.Proofs.Wasm.Acceptor.w_callI32 hj hx hf hS hpre hpost k

end Silmaril.Wasm.Acceptor
