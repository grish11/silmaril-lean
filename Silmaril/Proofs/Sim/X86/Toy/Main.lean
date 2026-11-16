module

public import Silmaril.Proofs.Sim.X86.Toy.Wasm

/-!
# The toy `f`: every dispatcher entry, by cut points

**`toy_entries`**: from a `JT k`-store, the entry at RIP evaluates to a `JT k'`-store with
`k' < k`, or RIP is the caller's return address (no entry matches) and `QT` holds. One case per
cut point: the entry's straight-line Wasm evaluation (`Steps`), then the next cut point's
assertion (address and stack arithmetic by `simp`/`bv_omega`, memory slots by
`ld_same`/`ld_keep`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.Toy

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Sim.X86.SumTo (tri tri_step b64_xor_one)
open Silmaril.Wasm.Logic.Core (exec Post)

variable {H : Type} {f : Frame}

section Stack

variable {s : Store H} {R : Reg → Word} {ip ax di rsp bx r12 zf : Word} {B : ByteArray} {sp0 : Word}

/-- `push r` from a `TV` store: the stored slot and the next `TV` store. -/
theorem TV.push_step (hW : (toyWin sp0).Ok) (hV : TV s f R ip ax di rsp bx r12 zf B) {sp : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) {r : Reg} {v : Word}
    (hr : gval s f (.reg r) = some (Val.i64 v)) (hh : (toyWin sp0).Holds (sp - 8#64)) {o : Nat}
    (ho : (sp - 8#64).toNat - (toyWin sp0).lo.toNat = o) (len : Nat) :
    ∃ s' B', exec s f [] (storeCode (toyWin sp0) rspDown [gget (.reg r)] ++ rspDown ++
        [gset (.reg .rsp)] ++ nextCode len) = some (s', f, []) ∧
      Memory.store B o (count := 8) v = some B' ∧
      TV s' f R (ip + BitVec.ofNat 64 len) ax di (sp - 8#64) bx r12 zf B' := by
  obtain ⟨hl, hip, -, -, -, -, -, -, -, hwb, hsz⟩ := id hV
  obtain ⟨s', B', he, hst, hwb', hl', hsp', hip', hSm⟩ := push_wstep hW hl hwb hsz hsp hip hr hh len
  have hst' : Memory.store B o (count := 8) v = some B' := ho ▸ hst
  exact ⟨s', B', he, hst', hV.keep hl' hSm hsp' hip' hwb' (by rw [size_keep hst]; exact hsz)⟩

/-- `call rel` from a `TV` store: the stored return address and the next `TV` store. -/
theorem TV.call_step (hW : (toyWin sp0).Ok) (hV : TV s f R ip ax di rsp bx r12 zf B) {sp : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hh : (toyWin sp0).Holds (sp - 8#64))
    {o : Nat} (ho : (sp - 8#64).toNat - (toyWin sp0).lo.toNat = o) (len : Nat) (rel : BitVec 32)
    {c : Word} (hc : ip + BitVec.ofNat 64 len = c) :
    ∃ s' B', exec s f [] (storeCode (toyWin sp0) rspDown [gget .rip, c64 (BitVec.ofNat 64 len),
        b64op .add] ++ rspDown ++ [gset (.reg .rsp), gget .rip,
          c64 (BitVec.ofNat 64 len + rel.signExtend 64), b64op .add, gset .rip]) = some (s', f, []) ∧
      Memory.store B o (count := 8) c = some B' ∧
      TV s' f R (ip + (BitVec.ofNat 64 len + rel.signExtend 64)) ax di (sp - 8#64) bx r12 zf B' := by
  obtain ⟨hl, hip, -, -, -, -, -, -, -, hwb, hsz⟩ := id hV
  obtain ⟨s', B', he, hst, hwb', hl', hsp', hip', hSm⟩ := call_wstep hW hl hwb hsz hsp hip hh len rel
  have hst' : Memory.store B o (count := 8) c = some B' := ho ▸ hc ▸ hst
  exact ⟨s', B', he, hst', hV.keep hl' hSm hsp' hip' hwb' (by rw [size_keep hst]; exact hsz)⟩

/-- `pop r12` from a `TV` store whose slot at `rsp` holds `v`. -/
theorem TV.pop_r12_step (hW : (toyWin sp0).Ok) (hV : TV s f R ip ax di rsp bx r12 zf B) {sp : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hh : (toyWin sp0).Holds sp) {o : Nat}
    (ho : sp.toNat - (toyWin sp0).lo.toNat = o) {v : Word} (hv : Ld B o v) (len : Nat) :
    ∃ s', exec s f [] (loadCode (toyWin sp0) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8,
        b64op .add, gset (.reg .rsp), gset (.reg .r12)] ++ nextCode len) = some (s', f, []) ∧
      TV s' f R (ip + BitVec.ofNat 64 len) ax di (sp + 8#64) bx v zf B := by
  obtain ⟨hl, hip, -, -, -, -, -, -, -, hwb, hsz⟩ := id hV
  obtain ⟨s', w, he, hw, hwb', hl', hsp', hrv, hip', hSm⟩ := pop_wstep hW hl hwb hsz
    (r := .r12) (by decide) hsp hip hh len
  have hv' : Memory.load B (sp.toNat - (toyWin sp0).lo.toNat) 8 = some v := ho ▸ hv
  have hwv : w = v := Option.some.inj (hw.symm.trans hv')
  have hV' := hV.keepR hl' (.inr rfl) hSm hsp' hip' (hwv ▸ hrv) hwb'
  exact ⟨s', he, by simpa only [reduceCtorEq, ite_false, ite_true] using hV'⟩

/-- `pop rbx` from a `TV` store whose slot at `rsp` holds `v`. -/
theorem TV.pop_rbx_step (hW : (toyWin sp0).Ok) (hV : TV s f R ip ax di rsp bx r12 zf B) {sp : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hh : (toyWin sp0).Holds sp) {o : Nat}
    (ho : sp.toNat - (toyWin sp0).lo.toNat = o) {v : Word} (hv : Ld B o v) (len : Nat) :
    ∃ s', exec s f [] (loadCode (toyWin sp0) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8,
        b64op .add, gset (.reg .rsp), gset (.reg .rbx)] ++ nextCode len) = some (s', f, []) ∧
      TV s' f R (ip + BitVec.ofNat 64 len) ax di (sp + 8#64) v r12 zf B := by
  obtain ⟨hl, hip, -, -, -, -, -, -, -, hwb, hsz⟩ := id hV
  obtain ⟨s', w, he, hw, hwb', hl', hsp', hrv, hip', hSm⟩ := pop_wstep hW hl hwb hsz
    (r := .rbx) (by decide) hsp hip hh len
  have hv' : Memory.load B (sp.toNat - (toyWin sp0).lo.toNat) 8 = some v := ho ▸ hv
  have hwv : w = v := Option.some.inj (hw.symm.trans hv')
  have hV' := hV.keepR hl' (.inl rfl) hSm hsp' hip' (hwv ▸ hrv) hwb'
  exact ⟨s', he, by simpa only [reduceCtorEq, ite_false, ite_true] using hV'⟩

/-- `ret` from a `TV` store whose slot at `rsp` holds the return address `v`. -/
theorem TV.ret_step (hW : (toyWin sp0).Ok) (hV : TV s f R ip ax di rsp bx r12 zf B) {sp : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hh : (toyWin sp0).Holds sp) {o : Nat}
    (ho : sp.toNat - (toyWin sp0).lo.toNat = o) {v : Word} (hv : Ld B o v) :
    ∃ s', exec s f [] (loadCode (toyWin sp0) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8,
        b64op .add, gset (.reg .rsp), gset .rip]) = some (s', f, []) ∧
      TV s' f R v ax di (sp + 8#64) bx r12 zf B := by
  obtain ⟨hl, -, -, -, -, -, -, -, -, hwb, hsz⟩ := id hV
  obtain ⟨s', w, he, hw, hwb', hl', hsp', hip', hSm⟩ := ret_wstep hW hl hwb hsz hsp hh
  have hv' : Memory.load B (sp.toNat - (toyWin sp0).lo.toNat) 8 = some v := ho ▸ hv
  have hwv : w = v := Option.some.inj (hw.symm.trans hv')
  exact ⟨s', he, hV.keep hl' hSm hsp' (hwv ▸ hip') hwb' hsz⟩

end Stack

/-- The claim of `toy_entries` at the entry `w`: its code evaluates to a `JT k'`-store with
`k' < k`, or no entry matches and `QT` holds. -/
abbrev EntryT (b sp ret : Word) (f : Frame) (R : Reg → Word) (k : Nat) (s : Store H) (w : Word) :
    Prop :=
  match lookupC (compileTabM (toyWin sp) (toyTab b)) w with
  | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, JT b sp ret f R k' s'
  | none => QT sp ret R s f (.normal [])

set_option maxHeartbeats 1000000 in
/-- **Every entry of the dispatcher of `f`**: a Wasm cut-point argument. -/
theorem toy_entries (b sp ret : Word) (R : Reg → Word) (h32 : 32 ≤ sp.toNat)
    (h8 : sp.toNat + 8 ≤ 2 ^ 64) (hret : 0x42 ≤ (ret - b).toNat) :
    ∀ k (s : Store H), JT b sp ret f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (toyTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧
          ∃ k' < k, JT b sp ret f R k' s'
      | none => QT sp ret R s f (.normal []) := by
  rintro k s ⟨ip, ax, di, rsp, bx, r12, zf, B, hV, hc⟩
  refine ⟨ip, hV.2.1, ?_⟩
  show EntryT b sp ret f R k s ip
  have hW : (toyWin sp).Ok := toyWin_ok h32 h8
  obtain ⟨hl, -, -, -, hsp, hbx, hr12, -, -, hwb, hsz⟩ := id hV
  have hne : ∀ c : Word, c.toNat < 0x42 → (ret = b + c) = False := fun c hc =>
    eq_false (by rintro rfl; simp at hret; omega)
  have hne0 : (ret = b) = False := eq_false (by rintro rfl; simp at hret)
  obtain ⟨h32m, ⟨rfl, hr, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, h24, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ |
    ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hle, rfl, rfl⟩ | ⟨rfl, hle, rfl, rfl, rfl⟩ |
      ⟨rfl, hnz, hle, rfl, rfl⟩ | ⟨rfl, hnz, hle, rfl, rfl⟩ | ⟨rfl, hlt, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ | ⟨rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ |
    ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ |
    ⟨rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ | ⟨rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ |
    ⟨rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩ | ⟨rfl, rfl, rfl, rfl, h24, rfl⟩ |
    ⟨rfl, hr, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ :
      CP b sp ret R k ip ax di rsp bx r12 zf B := hc
  · -- F0: push rbx
    show EntryT b sp ret f R _ s (b + 0x1d)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.push_step hW (sp := sp) (by rw [← hr]; exact hsp) hbx
      (holds_sp h32 h8 8#64 (by decide)) (by simp only [toyWin]; bv_omega : _ = 24) 1
    refine ⟨s', he, _, (by omega : 5 * (R .rdi).toNat + 28 < 5 * (R .rdi).toNat + 29), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨ld_keep hst (by omega) h32m,
      Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, rfl, ld_same hst, rfl⟩)⟩
  · -- F1: push r12
    show EntryT b sp ret f R _ s (b + 0x1e)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.push_step hW hsp hr12
      (by simp only [Win.Holds, toyWin]; bv_omega) (by simp only [toyWin]; bv_omega : _ = 16) 2
    refine ⟨s', he, _, (by omega : 5 * (R .rdi).toNat + 27 < 5 * (R .rdi).toNat + 28), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    refine ⟨ld_keep hst (by omega) h32m, ?_⟩
    exact Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl, rfl, ⟨ld_keep hst (by omega) h24, ld_same hst⟩, rfl⟩))
  · -- F2: sub $8, %rsp
    show EntryT b sp ret f R _ s (b + 0x20)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_sub_rsp hV
    refine ⟨s', he, _, (by omega : 5 * (R .rdi).toNat + 26 < 5 * (R .rdi).toNat + 27), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩)))⟩
  · -- F3: mov %rsi, %rbx
    show EntryT b sp ret f R _ s (b + 0x24)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_rbx_rsi hV
    refine ⟨s', he, _, (by omega : 5 * (R .rdi).toNat + 25 < 5 * (R .rdi).toNat + 26), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩))))⟩
  · -- F4: call sum_to
    show EntryT b sp ret f R _ s (b + 0x27)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.call_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 0) 5 0xffffffd4
      (by simp [BitVec.add_assoc] : b + 0x27 + BitVec.ofNat 64 5 = b + 0x2c)
    refine ⟨s', he, _, (by omega : 5 * (R .rdi).toNat + 24 < 5 * (R .rdi).toNat + 25), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    refine ⟨ld_keep hst (by omega) h32m, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by bv_omega, rfl, rfl, ⟨ld_keep hst (by omega) h24, ld_keep hst (by omega) h16⟩, ld_same hst, Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl⟩⟩)))))
  · -- sum_to: mov $0, %rax (`b` is named `ip` here)
    show EntryT ip sp ret f R _ s ip
    simp only [EntryT, ctab_eq, lookupC, left_eq_add, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov0 hV
    refine ⟨s', he, _, (by omega : 5 * (R .rdi).toNat + 23 < 5 * (R .rdi).toNat + 24), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inl ⟨by simp [], le_rfl, by simp, rfl⟩)⟩)))))⟩
  · -- sum_to: test %rdi, %rdi
    show EntryT b sp ret f R _ s (b + 0x07)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_test hV
    refine ⟨s', he, _, (by omega : 5 * di.toNat + 22 < 5 * di.toNat + 23), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], hle, rfl, rfl, rfl⟩))⟩)))))⟩
  · -- sum_to: je
    show EntryT b sp ret f R _ s (b + 0x0a)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_je hV
    cases hz : (di == 0)
    · have hnz : di ≠ 0 := by simpa using hz
      refine ⟨s', he, _, (by omega : 5 * di.toNat + 21 < 5 * di.toNat + 22), _, _, _, _,
        _, _, _, _, hV', ?_⟩
      dsimp only [CP]
      exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [jcc_bits, hz]; simp [BitVec.add_assoc], hnz, hle, rfl, rfl⟩)))⟩)))))⟩
    · have h0d : di = 0 := by simpa using hz
      refine ⟨s', he, _, (by simp [h0d] : 21 < 5 * di.toNat + 22), _, _, _, _,
        _, _, _, _, hV', ?_⟩
      dsimp only [CP]
      exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by rw [jcc_bits, hz]; simp [BitVec.add_assoc], by simp [h0d, tri], rfl⟩))))))⟩)))))⟩
  · -- sum_to: add %rdi, %rax
    show EntryT b sp ret f R _ s (b + 0x0c)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_add_rax_rdi hV
    refine ⟨s', he, _, (by omega : 5 * di.toNat + 20 < 5 * di.toNat + 21), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], hnz, hle, rfl, rfl⟩))))⟩)))))⟩
  · -- sum_to: sub $1, %rdi
    show EntryT b sp ret f R _ s (b + 0x0f)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_sub_rdi hV
    have hk0 : di.toNat ≠ 0 := fun e => hnz (BitVec.eq_of_toNat_eq (by simpa using e))
    have h1 : (di - 1).toNat = di.toNat - 1 := by bv_omega
    refine ⟨s', he, _, (by rw [h1]; omega : 5 * (di - 1).toNat + 24 < 5 * di.toNat + 20), _, _, _,
      _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by rw [h1]; omega, tri_step _ _ hnz hle, rfl⟩)))))⟩)))))⟩
  · -- sum_to: jmp
    show EntryT b sp ret f R _ s (b + 0x13)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_jmp hV
    refine ⟨s', he, _, (by omega : 5 * di.toNat + 23 < 5 * di.toNat + 24), _, _, _, _,
      _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by omega, rfl, rfl⟩)⟩)))))⟩
  · -- sum_to: ret
    show EntryT b sp ret f R _ s (b + 0x15)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.ret_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 0) h0
    refine ⟨s', he, _, (by omega : 15 < 21), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by bv_omega, rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩))))))⟩
  · -- F5: mov %rax, %r12
    show EntryT b sp ret f R _ s (b + 0x2c)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_r12_rax hV
    refine ⟨s', he, _, (by omega : 14 < 15), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩)))))))⟩
  · -- F6: mov %rbx, %rdi
    show EntryT b sp ret f R _ s (b + 0x2f)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_rdi_rbx hV
    refine ⟨s', he, _, (by omega : 13 < 14), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, ⟨h24, h16⟩, rfl⟩))))))))⟩
  · -- F7: call dbl
    show EntryT b sp ret f R _ s (b + 0x32)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.call_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 0) 5 0xffffffdf
      (by simp [BitVec.add_assoc] : b + 0x32 + BitVec.ofNat 64 5 = b + 0x37)
    refine ⟨s', he, _, (by omega : 12 < 13), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    refine ⟨ld_keep hst (by omega) h32m, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by bv_omega, rfl, rfl, ⟨ld_keep hst (by omega) h24, ld_keep hst (by omega) h16⟩, ld_same hst, Or.inl ⟨by simp [BitVec.add_assoc], rfl⟩⟩)))))))))
  · -- dbl: mov %rdi, %rax
    show EntryT b sp ret f R _ s (b + 0x16)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_rax_rdi hV
    refine ⟨s', he, _, (by omega : 11 < 12), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl⟩)⟩)))))))))⟩
  · -- dbl: add %rax, %rax
    show EntryT b sp ret f R _ s (b + 0x19)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_add_rax_rax hV
    refine ⟨s', he, _, (by omega : 10 < 11), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨h24, h16⟩, h0, Or.inr (Or.inr (⟨by simp [BitVec.add_assoc], rfl, rfl⟩))⟩)))))))))⟩
  · -- dbl: ret
    show EntryT b sp ret f R _ s (b + 0x1c)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.ret_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 0) h0
    refine ⟨s', he, _, (by omega : 9 < 10), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by bv_omega, rfl, rfl, ⟨h24, h16⟩, rfl⟩))))))))))⟩
  · -- F8: add %r12, %rax
    show EntryT b sp ret f R _ s (b + 0x37)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_add_rax_r12 hV
    refine ⟨s', he, _, (by omega : 8 < 9), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, ⟨h24, h16⟩, rfl⟩)))))))))))⟩
  · -- F9: add $8, %rsp
    show EntryT b sp ret f R _ s (b + 0x3a)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_add_rsp hV
    refine ⟨s', he, _, (by omega : 7 < 8), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, ⟨h24, h16⟩, rfl⟩))))))))))))⟩
  · -- F10: pop %r12
    show EntryT b sp ret f R _ s (b + 0x3e)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.pop_r12_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 16) h16 2
    refine ⟨s', he, _, (by omega : 6 < 7), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl, h24, rfl⟩)))))))))))))⟩
  · -- F11: pop %rbx
    show EntryT b sp ret f R _ s (b + 0x40)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.pop_rbx_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 24) h24 1
    refine ⟨s', he, _, (by omega : 5 < 6), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl, rfl, rfl⟩))))))))))))))⟩
  · -- F12: ret
    show EntryT b sp ret f R _ s (b + 0x41)
    simp only [EntryT, ctab_eq, lookupC, add_right_inj, add_eq_left, BitVec.reduceEq,
      ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.ret_step hW (sp := sp) (by rw [← hr]; exact hsp)
      (by simp only [Win.Holds, toyWin]; bv_omega) (by simp only [toyWin]; bv_omega : _ = 32) h32m
    refine ⟨s', he, 0, (by omega : 0 < 5), _, _, _, _, _, _, _, _, hV', ?_⟩
    dsimp only [CP]
    exact ⟨h32m, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl, rfl, rfl⟩)))))))))))))))⟩
  · -- returned: no entry matches
    show EntryT b sp ip f R k s ip
    have e7 : (ip = b + 7) = False := hne 7 (by decide)
    have e10 : (ip = b + 10) = False := hne 10 (by decide)
    have e12 : (ip = b + 12) = False := hne 12 (by decide)
    have e15 : (ip = b + 15) = False := hne 15 (by decide)
    have e19 : (ip = b + 19) = False := hne 19 (by decide)
    have e21 : (ip = b + 21) = False := hne 21 (by decide)
    have e22 : (ip = b + 22) = False := hne 22 (by decide)
    have e25 : (ip = b + 25) = False := hne 25 (by decide)
    have e28 : (ip = b + 28) = False := hne 28 (by decide)
    have e29 : (ip = b + 29) = False := hne 29 (by decide)
    have e30 : (ip = b + 30) = False := hne 30 (by decide)
    have e32 : (ip = b + 32) = False := hne 32 (by decide)
    have e36 : (ip = b + 36) = False := hne 36 (by decide)
    have e39 : (ip = b + 39) = False := hne 39 (by decide)
    have e44 : (ip = b + 44) = False := hne 44 (by decide)
    have e47 : (ip = b + 47) = False := hne 47 (by decide)
    have e50 : (ip = b + 50) = False := hne 50 (by decide)
    have e55 : (ip = b + 55) = False := hne 55 (by decide)
    have e58 : (ip = b + 58) = False := hne 58 (by decide)
    have e62 : (ip = b + 62) = False := hne 62 (by decide)
    have e64 : (ip = b + 64) = False := hne 64 (by decide)
    have e65 : (ip = b + 65) = False := hne 65 (by decide)
    simp only [EntryT, ctab_eq, lookupC, hne0, e7, e10, e12, e15, e19, e21, e22, e25, e28, e29, e30, e32, e36, e39, e44, e47, e50, e55, e58, e62, e64, e65, ite_false]
    exact ⟨rfl, di, zf, B, hV⟩

end Silmaril.Sim.X86.Toy
