module

public import Silmaril.Wasm.Examples.FarkasAccept.Defs
public import Silmaril.Wasm.Examples.Farkas.Thms
public import Silmaril.Wasm.Examples.LRAT.Thms

@[expose] public section

/-!
# The instantiated Farkas acceptor

Kernel-checked facts (`decide +kernel`) about the instance of `prog` computed by
`Silmaril.Wasm.Verify.instance?` (validation and instantiation against no imports): its exported
functions are `3`, `4` (`cabi_realloc`, `check`); every function's code, module instance and
type are the module's; the module instance resolves globals `0 … 4`, memories `0`, `1` and
functions `0 … 4` to the same addresses; the five globals hold their initial values and the two
memories have the module's types.

From them, the checker's fixture `accX top B₁` (`Silmaril.Wasm.Examples.Farkas.Fix`: the module
instance of the acceptor, the heap pointer `top` after the checker's four globals, the ABI memory
`B₁` after its memory) is `Fix.Ok`, and every store of the acceptor (`AccStore`) holds a
machine state of the checker in it with a one-page memory (`accStore_holds`).

`Instr` has no decidable equality, so code is compared with `ibeq`, a Boolean equality on the
instructions the acceptor uses, proved sound (`ibeqs_sound`).

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Verify Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.Farkas
open Silmaril.Wasm.Examples.FarkasAccept

/-! ## Comparing code -/

mutual
/-- Equality of instructions of the acceptor's fragment (`false` outside it). -/
def ibeq : Instr → Instr → Bool
  | .intConst .i32 a, .intConst .i32 b => a == b
  | .intConst .i64 a, .intConst .i64 b => a == b
  | .localGet x, .localGet y => x == y
  | .localSet x, .localSet y => x == y
  | .globalGet x, .globalGet y => x == y
  | .globalSet x, .globalSet y => x == y
  | .intBinOp t o, .intBinOp t' p => t == t' && o == p
  | .intRelOp t o, .intRelOp t' p => t == t' && o == p
  | .intTestOp t o, .intTestOp t' p => t == t' && o == p
  | .intLoad t none x a, .intLoad t' none y b => t == t' && x == y && a == b
  | .intStore t none x a, .intStore t' none y b => t == t' && x == y && a == b
  | .brIf l, .brIf m => l == m
  | .br l, .br m => l == m
  | .call x, .call y => x == y
  | .drop, .drop => true
  | .if_ .empty t e, .if_ .empty t' e' => ibeqs t t' && ibeqs e e'
  | .block .empty b, .block .empty b' => ibeqs b b'
  | .loop .empty b, .loop .empty b' => ibeqs b b'
  | _, _ => false
/-- Equality of instruction lists of the acceptor's fragment. -/
def ibeqs : List Instr → List Instr → Bool
  | [], [] => true
  | a :: as, b :: bs => ibeq a b && ibeqs as bs
  | _, _ => false
end

theorem ibeq_sound (a b : Instr) : ibeq a b = true → a = b := by
  apply ibeq.induct (motive_1 := fun a b => ibeq a b = true → a = b)
    (motive_2 := fun as bs => ibeqs as bs = true → as = bs)
  all_goals
    intros
    simp_all [ibeq, ibeqs]

theorem ibeqs_sound : ∀ (as bs : List Instr), ibeqs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ibeqs, Bool.and_eq_true] at h
    rw [ibeq_sound a b h.1, ibeqs_sound as bs h.2]
  | [], _ :: _, h => by simp [ibeqs] at h
  | _ :: _, [], h => by simp [ibeqs] at h

/-! ## The instance -/

/-- The module instance of its functions. -/
def accMi : ModuleInst := ((accS.funcs[0]?).map (·.module)).getD {}

/-- The code of a function instance and the module function it should be. -/
def codeMatches (fi : FuncInst Nat) (f : Func) : Bool :=
  match fi.code with
  | .wasm g => ibeqs g.body f.body && g.locals == f.locals && g.type == f.type
  | .host _ => false

/-- The type of the acceptor's two exports. -/
def ty4c : CCompType :=
  .func (Ty.ofList [.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)])
    (Ty.ofList [.num (.int .i32)])

/-- The function types of the checker's functions. -/
def farkasTys : List CCompType :=
  [.func (Ty.ofList [.num (.int .i64), .num (.int .i64)]) (Ty.ofList []),
    .func (Ty.ofList [.num (.int .i32), .num (.int .i64)]) (Ty.ofList []),
    .func (Ty.ofList []) (Ty.ofList [.num (.int .i32)])]

/-- The function types of the module's functions, in order. -/
def accTys : List CCompType := farkasTys ++ [ty4c, ty4c]

/-- Function `j` of the store, of the module and its type agree. -/
def accFnOk (j : Nat) : Bool :=
  match accS.funcs[j]?, prog.funcs[j]?, accTys[j]? with
  | some fi, some f, some ty => codeMatches fi f && fi.module == accMi && fi.type.expand? == some ty
  | _, _, _ => false

theorem acc_instance : (instance? prog).isSome = true := by decide +kernel

theorem acc_addrs : accI.addrs = [3, 4] := by decide +kernel

theorem acc_imports : accI.imports = [] := by decide +kernel

theorem acc_fnOk : (List.range 5).all accFnOk = true := by decide +kernel

theorem acc_funcs_length : accS.funcs.length = 5 := by decide +kernel

theorem acc_mi : accMi.globals = List.range 5 ∧ accMi.mems = [0, 1] ∧ accMi.funcs = List.range 5 := by
  decide +kernel

theorem acc_globals : accS.globals = [⟨accG32, Val.i32 0⟩, ⟨accG32, Val.i32 0⟩, ⟨accG64, Val.i64 0⟩,
    ⟨accG64, Val.i64 0⟩, ⟨accG32, Val.i32 (BitVec.ofNat 32 heapBase)⟩] := by decide +kernel

theorem acc_mems : accS.mems.map (·.type) = [farkasMemType, accMt] := by decide +kernel

/-! ## From the facts -/

/-- Function `j` of the instance. -/
theorem acc_fn (j : Nat) (hj : j < 5) : ∃ (fi : FuncInst Nat) (f : Func) (ty : CCompType),
    accS.funcs[j]? = some fi ∧ prog.funcs[j]? = some f ∧ accTys[j]? = some ty ∧
    fi.code = .wasm f ∧ fi.module = accMi ∧ Expand fi.type ty := by
  have h := List.all_eq_true.1 acc_fnOk j (List.mem_range.2 hj)
  unfold accFnOk at h
  split at h
  · rename_i fi f ty hfi hf hty
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hc, hm⟩, he⟩ := h
    refine ⟨fi, f, ty, hfi, hf, hty, ?_, hm, Expand.iff.2 he⟩
    unfold codeMatches at hc
    split at hc
    · rename_i g hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hb, hl⟩, ht⟩ := hc
      rw [hg]
      have hb' := ibeqs_sound _ _ hb
      cases g; cases f
      simp_all
    · cases hc
  · cases h

/-- **The checker's fixture in the acceptor**: the acceptor's module instance, the heap pointer
`top` after the checker's globals and the ABI memory `B₁` after its memory. -/
def accX (top : BitVec 32) (B₁ : ByteArray) : Fix :=
  ⟨accMi, [⟨accG32, Val.i32 top⟩], [⟨accMt, B₁⟩]⟩

theorem accX_ok (top : BitVec 32) (B₁ : ByteArray) : (accX top B₁).Ok :=
  ⟨⟨[4], by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.1]; rfl⟩,
    ⟨[1], by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.1]⟩⟩

/-- **Every store of the acceptor holds a checker state** in the fixture, with a one-page
memory. -/
theorem accStore_holds {s : Store Nat} {top : BitVec 32} {B₁ : ByteArray} (h : AccStore s top B₁) :
    ∃ m : Mach, HoldsX (accX top B₁) accS.funcs s m ∧ m.mem.size = 65536 := by
  obtain ⟨bad, hr, y, vb, hg⟩ := h.globals
  obtain ⟨B₀, hB₀, hm⟩ := h.mems
  refine ⟨⟨bad, hr, y, vb, B₀⟩, ⟨s, h.funcs, ?_⟩, hB₀⟩
  obtain ⟨⟩ := s
  simp only at hg hm
  simp only [withMachX, hg, hm]
  rfl

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
