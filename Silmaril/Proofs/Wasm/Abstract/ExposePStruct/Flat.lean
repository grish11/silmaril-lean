module

public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Lands

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: a checked flat instruction on a stack
with a passive suffix appends the suffix to every stack it ends with, and its results satisfy
the result invariant `GoodR`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Interp

variable {H : Type}

/-- Append `rest` to every stack a flow carries. -/
def wFl (rest : List Val) : Flow → Flow
  | .normal vs => .normal (vs ++ rest)
  | .brk l vs => .brk l (vs ++ rest)
  | .ret vs => .ret (vs ++ rest)
  | fl => fl

/-- `wFl` on an interpreter outcome. -/
def wE (rest : List Val) (t : Store H × Frame × Flow) : Store H × Frame × Flow :=
  (t.1, t.2.1, wFl rest t.2.2)

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}

set_option maxHeartbeats 1000000 in
theorem evalFlat_whisk {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {o : Option Nat}
    (hp : instrStackPure i = true) (hc : flatChkE ext F mi nl ret labels stk.length i = some o)
    (rest : List Val) :
    evalFlat s f (stk ++ rest) i = (evalFlat s f stk i).map (wE rest) := by
  cases i <;> simp only [instrStackPure, Bool.false_eq_true] at hp <;>
    (try cases ‹Option (PackSize × Signedness)›) <;>
    simp only [flatChkE, flatEff] at hc <;>
    rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
    simp [evalFlat, wE, wFl, Option.map_map, Function.comp_def] at hc ⊢
  all_goals first
    | ((repeat' split at hc) <;> simp_all; done)
    | (rcases truthy a with _ | (_ | _) <;> simp; done)
    | (congr 1; funext x; congr 1; funext y; split <;> rfl)
    | ((repeat' split) <;> simp_all [wE, wFl])

/-- The shape a checked flat instruction's flow has: a fallthrough at the checked height, a
branch with its label's arity, a return with the result arity. -/
def FlGood (labels : List Nat) (ret : Nat) (o : Option Nat) : Flow → Prop
  | .normal vs => o = some vs.length
  | .brk l vs => ∃ n, labels[l]? = some n ∧ n ≤ vs.length
  | .ret vs => ret ≤ vs.length
  | _ => True

theorem tableOk_get {labels : List Nat} {h : Nat} {ls : List LabelIdx} {d : LabelIdx} {k : Nat}
    (ht : tableOk labels h (d :: ls) = true) :
    ∃ n, labels[((ls[k]?).getD d).toNat]? = some n ∧ n ≤ h := by
  have hm : (ls[k]?).getD d ∈ d :: ls := by
    cases hk : ls[k]? with
    | none => exact List.mem_cons_self
    | some l => exact List.mem_cons_of_mem _ (List.mem_of_getElem? hk)
  have := List.all_eq_true.1 ht _ hm
  revert this
  cases labels[((ls[k]?).getD d).toNat]? with
  | none => simp
  | some n => simp

set_option linter.unusedTactic false in
set_option maxHeartbeats 1000000 in
theorem evalFlat_flGood {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr}
    {o : Option Nat} {fl : Flow} (hp : instrStackPure i = true)
    (hc : flatChkE ext F mi nl ret labels stk.length i = some o)
    (he : evalFlat s f stk i = some (s', f', fl)) : FlGood labels ret o fl := by
  cases i <;> simp only [instrStackPure, Bool.false_eq_true] at hp <;>
    (try cases ‹Option (PackSize × Signedness)›) <;>
    simp only [flatChkE, flatEff] at hc <;>
    rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
    simp [evalFlat] at hc he
  all_goals first
    | (simp_all [FlGood]; done)
    | (obtain ⟨_, _, -, -, -, rfl⟩ := he; simp_all [FlGood]; done)
    | (obtain ⟨k, -, -, -, rfl⟩ := he; simpa [FlGood] using tableOk_get (k := k.toNat) hc.1)
    | skip
  all_goals repeat' (first | split at he | split at hc | simp only [Option.bind_eq_some_iff] at he)
  all_goals (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at *)
  all_goals repeat' (first | casesm _ ∧ _ | casesm _ ∨ _ | casesm Exists _)
  all_goals subst_vars
  all_goals simp_all [FlGood]
  all_goals (try casesm* _ ∧ _)
  all_goals (try omega)
  all_goals (split at * <;> simp only [Option.some.injEq, Prod.mk.injEq] at * <;>
    casesm* _ ∧ _ <;> subst_vars <;> simp)

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct
