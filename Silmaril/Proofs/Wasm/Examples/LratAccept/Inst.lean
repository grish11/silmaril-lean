module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Realloc
public import Silmaril.Proofs.Wasm.Examples.LratAccept.Nested

@[expose] public section

/-!
# The instantiated acceptor

Kernel-checked facts (`decide +kernel`) about the instance of `prog` computed by
`Silmaril.Wasm.Verify.instance?` (validation and instantiation against no imports): its exported
functions are `10`, `11`, `12` (`cabi_realloc`, `check-stream`, `check-nested`); every function's
code, module instance and type are the module's; the module instance resolves globals `0 … 8`,
memories `0`, `1` and functions `0 … 12` to the same addresses; the nine globals hold their
initial values and the two memories have the module's types. From them, the fixture `accX top B₁`
(the instance's functions, the LRAT state, the heap pointer `top`, the ABI memory `B₁`) holds
the LRAT code (`accX_code`), resolves as `MiOk` says (`accX_mi`) and has the ABI memory and the
heap pointer (`accX_abi`).

`Instr` has no decidable equality, so code is compared with `ibeq'`, a Boolean equality on the
instructions the acceptor uses (the LRAT fragment and `call`), proved sound (`ibeqs'_sound`).

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Verify Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.LRAT
open Silmaril.Wasm.Examples.LratAccept

/-! ## Comparing code -/

mutual
/-- Equality of instructions of the acceptor's fragment (`false` outside it). -/
def ibeq' : Instr → Instr → Bool
  | .intConst .i32 a, .intConst .i32 b => a == b
  | .localGet x, .localGet y => x == y
  | .localSet x, .localSet y => x == y
  | .globalGet x, .globalGet y => x == y
  | .globalSet x, .globalSet y => x == y
  | .intBinOp .i32 o, .intBinOp .i32 p => o == p
  | .intRelOp .i32 o, .intRelOp .i32 p => o == p
  | .intTestOp .i32 o, .intTestOp .i32 p => o == p
  | .intLoad .i32 none x a, .intLoad .i32 none y b => x == y && a == b
  | .intStore .i32 none x a, .intStore .i32 none y b => x == y && a == b
  | .brIf l, .brIf m => l == m
  | .br l, .br m => l == m
  | .call x, .call y => x == y
  | .if_ .empty t e, .if_ .empty t' e' => ibeqs' t t' && ibeqs' e e'
  | .block .empty b, .block .empty b' => ibeqs' b b'
  | .loop .empty b, .loop .empty b' => ibeqs' b b'
  | _, _ => false
/-- Equality of instruction lists of the acceptor's fragment. -/
def ibeqs' : List Instr → List Instr → Bool
  | [], [] => true
  | a :: as, b :: bs => ibeq' a b && ibeqs' as bs
  | _, _ => false
end

theorem ibeq'_sound (a b : Instr) : ibeq' a b = true → a = b := by
  apply ibeq'.induct (motive_1 := fun a b => ibeq' a b = true → a = b)
    (motive_2 := fun as bs => ibeqs' as bs = true → as = bs)
  all_goals
    intros
    simp_all [ibeq', ibeqs']

theorem ibeqs'_sound : ∀ (as bs : List Instr), ibeqs' as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ibeqs', Bool.and_eq_true] at h
    rw [ibeq'_sound a b h.1, ibeqs'_sound as bs h.2]
  | [], _ :: _, h => by simp [ibeqs'] at h
  | _ :: _, [], h => by simp [ibeqs'] at h

/-! ## The instance -/

/-- The module instance of its functions. -/
def accMi : ModuleInst := ((accS.funcs[0]?).map (·.module)).getD {}

/-- The code of a function instance and the module function it should be. -/
def codeMatches' (fi : FuncInst Nat) (f : Func) : Bool :=
  match fi.code with
  | .wasm g => ibeqs' g.body f.body && g.locals == f.locals && g.type == f.type
  | .host _ => false

/-- The type of the acceptor's three exports. -/
def ty4c : CCompType :=
  .func (Ty.ofList [.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)])
    (Ty.ofList [.num (.int .i32)])

/-- The function types of the module's functions, in order. -/
def accTys : List CCompType := lratTys ++ [ty4c, ty4c, ty4c]

/-- Function `j` of the store, of the module and its type agree. -/
def accFnOk (j : Nat) : Bool :=
  match accS.funcs[j]?, prog.funcs[j]?, accTys[j]? with
  | some fi, some f, some ty => codeMatches' fi f && fi.module == accMi && fi.type.expand? == some ty
  | _, _, _ => false

theorem acc_instance : (instance? prog).isSome = true := by decide +kernel

theorem acc_addrs : accI.addrs = [10, 11, 12] := by decide +kernel

theorem acc_imports : accI.imports = [] := by decide +kernel

theorem acc_fnOk : (List.range 13).all accFnOk = true := by decide +kernel

theorem acc_funcs_length : accS.funcs.length = 13 := by decide +kernel

theorem acc_mi : accMi.globals = List.range 9 ∧ accMi.mems = [0, 1] ∧ accMi.funcs = List.range 13 := by
  decide +kernel

theorem acc_globals : accS.globals = (G₀ ++ [16]).map fun v => ⟨accGt, Val.i32 v⟩ := by decide +kernel

theorem acc_mems : accS.mems.map (·.type) = [lratMemType, accMt] := by decide +kernel

/-! ## From the facts -/

/-- Function `j` of the instance. -/
theorem acc_fn (j : Nat) (hj : j < 13) : ∃ (fi : FuncInst Nat) (f : Func) (ty : CCompType),
    accS.funcs[j]? = some fi ∧ prog.funcs[j]? = some f ∧ accTys[j]? = some ty ∧
    fi.code = .wasm f ∧ fi.module = accMi ∧ Expand fi.type ty := by
  have h := List.all_eq_true.1 acc_fnOk j (List.mem_range.2 hj)
  unfold accFnOk at h
  split at h
  · rename_i fi f ty hfi hf hty
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hc, hm⟩, he⟩ := h
    refine ⟨fi, f, ty, hfi, hf, hty, ?_, hm, Expand.iff.2 he⟩
    unfold codeMatches' at hc
    split at hc
    · rename_i g hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hb, hl⟩, ht⟩ := hc
      rw [hg]
      have hb' := ibeqs'_sound _ _ hb
      cases g; cases f
      simp_all
    · cases hc
  · cases h

/-- The acceptor's fixture: the instance's functions and module instance, the heap pointer `top`
and the ABI memory `B₁` after the LRAT state. -/
def accX (top : BitVec 32) (B₁ : ByteArray) : Fix Nat :=
  ⟨accS.funcs, accMi, accGt, lratMemType, [⟨accGt, Val.i32 top⟩], [⟨accMt, B₁⟩]⟩

theorem accX_mi (top : BitVec 32) (B₁ : ByteArray) : MiOk (accX top B₁) :=
  ⟨fun k hk => by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.1, List.getElem?_range (by omega)],
    by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.1]; rfl⟩

theorem lratModule_funcs (j : Nat) (hj : j < 10) : prog.funcs[j]? = lratModule.funcs[j]? := by
  have hl : lratModule.funcs.length = 10 := rfl
  simp only [prog]
  rw [List.getElem?_append_left (by omega)]

theorem accTys_lt (j : Nat) (hj : j < 10) : accTys[j]? = lratTys[j]? := by
  have hl : lratTys.length = 10 := rfl
  simp only [accTys]
  rw [List.getElem?_append_left (by omega)]

theorem accX_code (top : BitVec 32) (B₁ : ByteArray) : CodeOk (accX top B₁) where
  fn j hj := by
    obtain ⟨fi, f, ty, h1, h2, h3, h4, h5, h6⟩ := acc_fn j (by omega)
    exact ⟨fi, f, ty, h1, by rw [← lratModule_funcs j hj]; exact h2,
      by rw [← accTys_lt j hj]; exact h3, h4, h5, h6⟩
  addr j hj := by
    rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.2, List.getElem?_range (by omega)]

theorem accX_abi (top : BitVec 32) {B₁ : ByteArray} (hsz : B₁.size < 2 ^ 32) : Abi (accX top B₁) B₁ where
  mem1 := by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.1]; rfl
  mrest := ⟨accMt, rfl⟩
  glob8 := by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.1]; rfl
  grest := ⟨_, rfl⟩
  size := hsz

end Silmaril.Proofs.Wasm.Examples.LratAccept
