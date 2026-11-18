module

public import Silmaril.Sim.SysV.Defs

/-!
# Evaluating the wrapper code

* `exec1_lget`, `exec1_lset`, `exec1_ltee`, `exec1_shl`: the local and shift instructions.
* `nz_eq`, **`statusOf_eq_zero`**: a zero status word means `rsp` and the six callee-saved
  registers are unchanged.
* **`prologue_exec`**: from a store encoding the caller's registers `σ` and a frame holding the
  arguments, the prologue evaluates to a store encoding `entryCore d σ`, with the callee-saved
  registers and the entry stack pointer saved in locals 7..13 (`Saved`).
* **`epilogue_exec`**: from a store encoding the final registers, the epilogue pushes `rax` and
  `statusOf`.
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 exec_append exec_cons exec_nil localVal?)
open Silmaril.X86 (Reg State Word)
open Silmaril.Sim.X86.G

variable {H : Type} {s : Store H} {f : Frame}

/-! ## Instructions -/

theorem exec1_lget (rs : List Val) (i : Fin 16) {v : Val} (h : f.locals[i.val]? = some (some v)) :
    exec1 s f rs (lget i) = some (s, f, v :: rs) := by
  simp [lget, lidx, exec1, localVal?, Frame.local?, Idx.toNat, h]

theorem exec1_lset (rs : List Val) (i : Fin 16) (v : Val) (h : i.val < f.locals.length) :
    exec1 s f (v :: rs) (lset i) = some (s, f.setLocal (lidx i) v, rs) := by
  simp [lset, lidx, exec1, Silmaril.Wasm.Logic.Core.popV, Idx.toNat, h]

theorem exec1_ltee (rs : List Val) (i : Fin 16) (v : Val) (h : i.val < f.locals.length) :
    exec1 s f (v :: rs) (ltee i) = some (s, f.setLocal (lidx i) v, v :: rs) := by
  simp [ltee, lidx, exec1, Silmaril.Wasm.Logic.Core.popV, Idx.toNat, h]

theorem exec1_shl (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op .shl) =
      some (s, f, Val.i64 (x <<< (y.toNat % 64)) :: rs) := by
  rw [exec1_b64op]; rfl

theorem setLocal_locals (f : Frame) (i : Fin 16) (v : Val) :
    (f.setLocal (lidx i) v).locals = f.locals.set i.val (some v) := rfl

/-! ## The status word -/

theorem nz_eq (x : BitVec 64) : nz x = b64 !(x == 0#64) := by
  rw [nz, shr63, msb_or_neg]

theorem nz_shl_eq_zero {x : BitVec 64} {k : Nat} (hk : k < 64) (h : nz x <<< k = 0#64) : x = 0#64 := by
  rw [nz_eq] at h
  by_cases hx : x = 0#64
  · exact hx
  · exfalso
    have : (x == 0#64) = false := by simpa using hx
    rw [this] at h
    simp only [Bool.not_false, b64, ite_true] at h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_shiftLeft] at h'
    simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by omega : 0 < 64)] at h'
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)] at h'
    exact absurd h' (Nat.two_pow_pos k).ne'

theorem nz_xor {x y : BitVec 64} {k : Nat} (hk : k < 64) (h : nz (x ^^^ y) <<< k = 0#64) : x = y :=
  BitVec.xor_eq_zero_iff.mp (nz_shl_eq_zero hk h)

theorem or_eq_zero {x y : BitVec 64} (h : (x ||| y) = 0) : x = 0 ∧ y = 0 :=
  BitVec.or_eq_zero_iff.mp h

/-- **A zero status word**: `rsp` and the callee-saved registers are unchanged. -/
theorem statusOf_eq_zero {e g : Reg → Word} (h : statusOf e g = 0) :
    g .rsp = e .rsp ∧ g .rbx = e .rbx ∧ g .rbp = e .rbp ∧ g .r12 = e .r12 ∧ g .r13 = e .r13 ∧
      g .r14 = e .r14 ∧ g .r15 = e .r15 := by
  rw [statusOf] at h
  obtain ⟨h, h7⟩ := or_eq_zero h
  obtain ⟨h, h6⟩ := or_eq_zero h
  obtain ⟨h, h5⟩ := or_eq_zero h
  obtain ⟨h, h4⟩ := or_eq_zero h
  obtain ⟨h, h3⟩ := or_eq_zero h
  obtain ⟨h, h2⟩ := or_eq_zero h
  obtain ⟨-, h1⟩ := or_eq_zero h
  exact ⟨nz_xor (by omega) h1, nz_xor (by omega) h2, nz_xor (by omega) h3, nz_xor (by omega) h4,
    nz_xor (by omega) h5, nz_xor (by omega) h6, nz_xor (by omega) h7⟩

/-! ## The prologue -/

/-- Locals 7..13 hold the entry values of rbx rbp r12 r13 r14 r15 and rsp. -/
def Saved (f : Frame) (e : State) : Prop :=
  f.locals.length = 15 ∧
  f.locals[7]? = some (some (Val.i64 (e.read .rbx))) ∧ f.locals[8]? = some (some (Val.i64 (e.read .rbp))) ∧
  f.locals[9]? = some (some (Val.i64 (e.read .r12))) ∧ f.locals[10]? = some (some (Val.i64 (e.read .r13))) ∧
  f.locals[11]? = some (some (Val.i64 (e.read .r14))) ∧ f.locals[12]? = some (some (Val.i64 (e.read .r15))) ∧
  f.locals[13]? = some (some (Val.i64 (e.read .rsp)))

theorem list6 {α : Type} (l : List α) (h : l.length = 6) :
    ∃ a₀ a₁ a₂ a₃ a₄ a₅, l = [a₀, a₁, a₂, a₃, a₄, a₅] := by
  match l, h with
  | [a₀, a₁, a₂, a₃, a₄, a₅], _ => exact ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl⟩

theorem regArgs_length' (d : SysVCall) (h : d.intArgs.length ≤ 6) : d.regArgs.length = 6 := by
  simp only [SysVCall.regArgs, List.length_append, List.length_replicate]
  omega

theorem enc_frame {f' : Frame} (h : f'.module = f.module) {σ : State} (hE : Enc s f σ) :
    Enc s f' σ := by
  have hg : ∀ l, gval s f' l = gval s f l := fun l => by rw [gval_eq, gval_eq, h]
  obtain ⟨⟨ha, hi⟩, hr, hrip, h1, h2, h3, h4⟩ := hE
  refine ⟨⟨fun l => h ▸ ha l, fun l₁ l₂ a => h ▸ hi l₁ l₂ a⟩, fun r => (hg _).trans (hr r),
    (hg _).trans hrip, ?_, ?_, ?_, ?_⟩ <;> rw [hg] <;> assumption

theorem exec_lget_gset {rs : List Val} {i : Fin 16} {v : Val} (hl : Layout s f) (l : Loc)
    (hv : f.locals[i.val]? = some (some v)) (rest : List Instr) :
    exec s f rs (lget i :: gset l :: rest) = exec (upd s f l v) f rs rest := by
  rw [Silmaril.Wasm.Logic.Core.exec_cons_of_some (exec1_lget rs i hv),
    Silmaril.Wasm.Logic.Core.exec_cons_of_some (exec1_gset hl rs l v)]

theorem exec_gget_lset {rs : List Val} {i : Fin 16} {v : Val} (l : Loc) (hv : gval s f l = some v)
    (hi : i.val < f.locals.length) (rest : List Instr) :
    exec s f rs (gget l :: lset i :: rest) = exec s (f.setLocal (lidx i) v) rs rest := by
  rw [Silmaril.Wasm.Logic.Core.exec_cons_of_some (by rw [exec1_gget, hv]; rfl),
    Silmaril.Wasm.Logic.Core.exec_cons_of_some (exec1_lset rs i v hi)]

theorem gval_frame {f' : Frame} (h : f'.module = f.module) (l : Loc) : gval s f' l = gval s f l := by
  rw [gval_eq, gval_eq, h]

theorem frames_frame {s' : Store H} {f' : Frame} (hF : Frames s s' f') (h : f'.module = f.module) :
    Frames s s' f := by
  obtain ⟨a, b, c⟩ := hF
  exact ⟨a, b, fun x hx => c x (by rw [h]; exact hx)⟩

theorem layout_frame {f' : Frame} (h : f'.module = f.module) (hl : Layout s f) : Layout s f' :=
  ⟨fun l => h ▸ hl.addr l, fun l₁ l₂ a => h ▸ hl.inj l₁ l₂ a⟩

theorem upd_frame {f' : Frame} (h : f'.module = f.module) (l : Loc) (v : Val) :
    upd s f' l v = upd s f l v := by
  simp only [upd, h]

/-- `rsp := entrySp n rsp`. -/
theorem exec_spCode {σ : State} (hE : Enc s f σ) (n : Nat) (h14 : 14 < f.locals.length) :
    exec s f [] (spCode n) =
      some (upd s f (.reg .rsp) (Val.i64 (entrySp n (σ.read .rsp))),
        f.setLocal (lidx 14) (Val.i64 (σ.read .rsp - BitVec.ofNat 64 (8 * n))), []) := by
  have hl := hE.1
  have h14' : (f.setLocal (lidx 14) (Val.i64 (σ.read .rsp - BitVec.ofNat 64 (8 * n)))).locals[(14 : Fin 16).val]? =
      some (some (Val.i64 (σ.read .rsp - BitVec.ofNat 64 (8 * n)))) := by
    rw [setLocal_locals]; simp [h14]
  have hm : (f.setLocal (lidx 14) (Val.i64 (σ.read .rsp - BitVec.ofNat 64 (8 * n)))).module = f.module := rfl
  simp only [spCode, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gget, hE.2.1 .rsp, Option.map_some,
    exec1_c64, exec1_sub, exec1_ltee _ 14 _ h14, exec1_lget _ 14 h14', exec1_and,
    exec1_gset (layout_frame hm hl), Silmaril.Wasm.Logic.Core.exec_nil, upd_frame hm]
  rfl

/-- **The prologue.** -/
theorem prologue_exec {σ : State} (hE : Enc s f σ) {d : SysVCall} (hk : d.intArgs.length ≤ 6)
    (hL : ArgLocals f d) :
    ∃ s₁ f₁, exec s f [] (prologue d.stackArgs.length) = some (s₁, f₁, []) ∧
      f₁.module = f.module ∧ Enc s₁ f₁ (entryCore d σ) ∧ Frames s s₁ f ∧ Saved f₁ (entryCore d σ) := by
  obtain ⟨hlen, harg, htgt, -⟩ := hL
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, ha⟩ : ∃ a₀ a₁ a₂ a₃ a₄ a₅, d.regArgs = [a₀, a₁, a₂, a₃, a₄, a₅] :=
    list6 d.regArgs (regArgs_length' d hk)
  have harg' : ∀ i : Fin 6,
      f.locals[i.val]? = some (some (Val.i64 ([a₀, a₁, a₂, a₃, a₄, a₅].getD i.val 0))) := by
    rw [← ha]; exact harg
  have hl : Layout s f := hE.1
  -- spCode
  let E := entrySp d.stackArgs.length (σ.read .rsp)
  let f₀ := f.setLocal (lidx 14) (Val.i64 (σ.read .rsp - BitVec.ofNat 64 (8 * d.stackArgs.length)))
  have hm₀ : f₀.module = f.module := rfl
  have hlen₀ : f₀.locals.length = 15 := by
    show (f.setLocal _ _).locals.length = 15
    rw [setLocal_locals, List.length_set, hlen]
  have hloc₀ : ∀ i : Nat, i < 14 → f₀.locals[i]? = f.locals[i]? := by
    intro i hi
    show (f.setLocal _ _).locals[i]? = _
    rw [setLocal_locals]
    exact List.getElem?_set_ne (show (14 : Fin 16).val ≠ i by show 14 ≠ i; omega)
  let t₀ := upd s f (.reg .rsp) (Val.i64 E)
  have hsp : exec s f [] (spCode d.stackArgs.length) = some (t₀, f₀, []) :=
    exec_spCode hE d.stackArgs.length (by omega)
  let σ₀ := σ.write .rsp E
  have hE₀ : Enc t₀ f₀ σ₀ :=
    enc_frame hm₀ (enc_reg hE .rsp E σ₀ (regsAfter_write _ _ _ _ rfl) rfl rfl)
  -- argsCode
  have hv : ∀ (i : Fin 16) (a : Word), i.val < 14 → f.locals[i.val]? = some (some (Val.i64 a)) →
      f₀.locals[i.val]? = some (some (Val.i64 a)) := fun i a hi h => (hloc₀ i.val hi).trans h
  have h6 : f₀.locals[(6 : Fin 16).val]? = some (some (Val.i64 d.target)) := (hloc₀ 6 (by omega)).trans htgt
  -- the argument registers and rip
  let σ₁ := σ₀.write .rdi a₀
  let t₁ := upd t₀ f₀ (.reg .rdi) (Val.i64 a₀)
  have hE₁ : Enc t₁ f₀ σ₁ := enc_reg hE₀ .rdi a₀ σ₁ (regsAfter_write _ _ _ _ rfl) rfl rfl
  let σ₂ := σ₁.write .rsi a₁
  let t₂ := upd t₁ f₀ (.reg .rsi) (Val.i64 a₁)
  have hE₂ : Enc t₂ f₀ σ₂ := enc_reg hE₁ .rsi a₁ σ₂ (regsAfter_write _ _ _ _ rfl) rfl rfl
  let σ₃ := σ₂.write .rdx a₂
  let t₃ := upd t₂ f₀ (.reg .rdx) (Val.i64 a₂)
  have hE₃ : Enc t₃ f₀ σ₃ := enc_reg hE₂ .rdx a₂ σ₃ (regsAfter_write _ _ _ _ rfl) rfl rfl
  let σ₄ := σ₃.write .rcx a₃
  let t₄ := upd t₃ f₀ (.reg .rcx) (Val.i64 a₃)
  have hE₄ : Enc t₄ f₀ σ₄ := enc_reg hE₃ .rcx a₃ σ₄ (regsAfter_write _ _ _ _ rfl) rfl rfl
  let σ₅ := σ₄.write .r8 a₄
  let t₅ := upd t₄ f₀ (.reg .r8) (Val.i64 a₄)
  have hE₅ : Enc t₅ f₀ σ₅ := enc_reg hE₄ .r8 a₄ σ₅ (regsAfter_write _ _ _ _ rfl) rfl rfl
  let σ₆ := σ₅.write .r9 a₅
  let t₆ := upd t₅ f₀ (.reg .r9) (Val.i64 a₅)
  have hE₆ : Enc t₆ f₀ σ₆ := enc_reg hE₅ .r9 a₅ σ₆ (regsAfter_write _ _ _ _ rfl) rfl rfl
  let σe : State := { σ₆ with rip := d.target }
  have hσe : entryCore d σ = σe := by rw [entryCore, ha]; rfl
  let s₇ := upd t₆ f₀ .rip (Val.i64 d.target)
  have hE₇ : Enc s₇ f₀ (entryCore d σ) := by
    rw [hσe]; exact Enc.next hE₆ σe rfl rfl d.target rfl
  have hargs : exec t₀ f₀ [] argsCode = exec s₇ f₀ [] [] := by
    simp only [argsCode]
    rw [exec_lget_gset hE₀.1 _ (hv 0 a₀ (by decide) (harg' 0)),
      exec_lget_gset hE₁.1 _ (hv 1 a₁ (by decide) (harg' 1)),
      exec_lget_gset hE₂.1 _ (hv 2 a₂ (by decide) (harg' 2)),
      exec_lget_gset hE₃.1 _ (hv 3 a₃ (by decide) (harg' 3)),
      exec_lget_gset hE₄.1 _ (hv 4 a₄ (by decide) (harg' 4)),
      exec_lget_gset hE₅.1 _ (hv 5 a₅ (by decide) (harg' 5)), exec_lget_gset hE₆.1 _ h6]
  have hF : Frames s s₇ f := by
    have hF₀ : Frames s (upd s f (.reg .rsp) (Val.i64 E)) f₀ := by
      rw [← upd_frame hm₀]; exact (Frames.refl s f₀).upd (layout_frame hm₀ hl) _ _
    exact frames_frame ((((((((hF₀.upd hE₀.1 _ _).upd hE₁.1 _ _).upd hE₂.1 _ _).upd hE₃.1 _ _).upd
      hE₄.1 _ _).upd hE₅.1 _ _).upd hE₆.1 _ _)) hm₀
  -- the saves
  have hg : ∀ (f' : Frame) (r : Reg), f'.module = f.module →
      gval s₇ f' (.reg r) = some (Val.i64 ((entryCore d σ).read r)) := fun f' r h =>
    (gval_frame (h.trans hm₀.symm) _).trans (hE₇.2.1 r)
  let e := entryCore d σ
  let f₁ := f₀.setLocal (lidx 7) (Val.i64 (e.read .rbx))
  let f₂ := f₁.setLocal (lidx 8) (Val.i64 (e.read .rbp))
  let f₃ := f₂.setLocal (lidx 9) (Val.i64 (e.read .r12))
  let f₄ := f₃.setLocal (lidx 10) (Val.i64 (e.read .r13))
  let f₅ := f₄.setLocal (lidx 11) (Val.i64 (e.read .r14))
  let f₆ := f₅.setLocal (lidx 12) (Val.i64 (e.read .r15))
  let f₇ := f₆.setLocal (lidx 13) (Val.i64 (e.read .rsp))
  have hsaves : exec s₇ f₀ [] saveCode = exec s₇ f₇ [] [] := by
    simp only [saveCode]
    rw [exec_gget_lset _ (hg f₀ .rbx rfl) (by rw [hlen₀]; decide),
      exec_gget_lset _ (hg f₁ .rbp rfl) (by simp [f₁, setLocal_locals, hlen₀]),
      exec_gget_lset _ (hg f₂ .r12 rfl) (by simp [f₂, f₁, setLocal_locals, hlen₀]),
      exec_gget_lset _ (hg f₃ .r13 rfl) (by simp [f₃, f₂, f₁, setLocal_locals, hlen₀]),
      exec_gget_lset _ (hg f₄ .r14 rfl) (by simp [f₄, f₃, f₂, f₁, setLocal_locals, hlen₀]),
      exec_gget_lset _ (hg f₅ .r15 rfl) (by simp [f₅, f₄, f₃, f₂, f₁, setLocal_locals, hlen₀]),
      exec_gget_lset _ (hg f₆ .rsp rfl) (by simp [f₆, f₅, f₄, f₃, f₂, f₁, setLocal_locals, hlen₀])]
  refine ⟨s₇, f₇, ?_, rfl, enc_frame (f' := f₇) (f := f₀) rfl hE₇, hF, ?_⟩
  · rw [prologue, exec_append, exec_append, hsp]
    simp only
    rw [hargs, Silmaril.Wasm.Logic.Core.exec_nil]
    simp only
    rw [hsaves, Silmaril.Wasm.Logic.Core.exec_nil]
  · have hl7 : f₇.locals = (((((((f₀.locals.set 7 (some (Val.i64 (e.read .rbx)))).set 8
        (some (Val.i64 (e.read .rbp)))).set 9 (some (Val.i64 (e.read .r12)))).set 10
        (some (Val.i64 (e.read .r13)))).set 11 (some (Val.i64 (e.read .r14)))).set 12
        (some (Val.i64 (e.read .r15)))).set 13 (some (Val.i64 (e.read .rsp)))) := rfl
    simp only [Saved, hl7, List.length_set, hlen₀, List.getElem?_set, e]
    simp

/-! ## The epilogue -/

theorem exec_chk {rs : List Val} {l : Loc} {i : Fin 16} {x y : BitVec 64} (k acc : BitVec 64)
    (hx : gval s f l = some (Val.i64 x)) (hy : f.locals[i.val]? = some (some (Val.i64 y)))
    (rest : List Instr) :
    exec s f (Val.i64 acc :: rs) (chkCode l i k ++ rest) =
      exec s f (Val.i64 (acc ||| nz (x ^^^ y) <<< (k.toNat % 64)) :: rs) rest := by
  simp only [chkCode, nzCode, msbCode, List.cons_append, List.nil_append,
    Silmaril.Wasm.Logic.Core.exec_cons, exec1_gget, hx, Option.map_some, exec1_lget _ _ hy, exec1_xor,
    exec1_c64, exec1_sub, exec1_or, exec1_shr63, exec1_shl]
  rfl

/-- **The epilogue**: `rax` and the status word. -/
theorem epilogue_exec {σ' e : State} (hE : Enc s f σ') (hS : Saved f e) :
    exec s f [] epilogue =
      some (s, f, [Val.i64 (statusOf e.read σ'.read), Val.i64 (σ'.read .rax)]) := by
  obtain ⟨-, h7, h8, h9, h10, h11, h12, h13⟩ := hS
  have hr := hE.2.1
  simp only [epilogue, statusCode, List.append_assoc, List.cons_append, List.nil_append]
  rw [Silmaril.Wasm.Logic.Core.exec_cons_of_some (by rw [exec1_gget, hr]; rfl),
    Silmaril.Wasm.Logic.Core.exec_cons_of_some (exec1_c64 _ _ _ _),
    exec_chk _ _ (hr _) h13, exec_chk _ _ (hr _) h7, exec_chk _ _ (hr _) h8, exec_chk _ _ (hr _) h9,
    exec_chk _ _ (hr _) h10, exec_chk _ _ (hr _) h11, ← List.append_nil (chkCode (.reg .r15) 12 7),
    exec_chk _ _ (hr _) h12, Silmaril.Wasm.Logic.Core.exec_nil]
  rfl

end Silmaril.Sim.SysV
