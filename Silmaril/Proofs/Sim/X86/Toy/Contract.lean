module

public import Silmaril.Proofs.Sim.X86.Toy.X86
public import Silmaril.Machine.X86.Open9.Thms
public import Silmaril.Sim.X86.G.Thms

/-!
# The toy `f` as a System V function contract on `Open9.isa`

`toySpec`: entry = the toy's bytes at `rip - 0x1d` (code outside the stack window, no address
wrap), the stack window `[rsp - 32, rsp + 8)` readable, writable and backed, and the return
address outside the code; footprint = the window; post = `rax = (0 + ⋯ + rdi) + 2 · rsi`.
**`toySpec_total`** / `toyContract : FnContract Open9.isa` (total correctness):

* the run exists (`xrun_existsM`): termination from the Wasm measure of `toy_entries`, and x86
  progress (`toy_progress`: the two pushes and `sub` need no flags; afterwards the flags are
  defined);
* its result is the x86 problem's (`x86_solution`, from the Wasm solution);
* it is a run of the open machine (`run_of_xrunM`), writing only inside the window.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Toy

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State MState Byte sysv64)
open Silmaril.X86.Ext (Sz RM Result retire readRM writeRM aluStep)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Sim.X86.SumTo (tri)
open Silmaril.Machine.X86

/-- `push r` retires from any state whose push slot is in the window. -/
private theorem toy_push_exec {sp : Word} {σ : State} {mem : Silmaril.Process.Memory} {s : Store Nat}
    (hM : MemEnc s encFrameM mem (toyWin sp)) {r : Reg} {n : Nat}
    (hw : ∀ a k, access (.push r) σ n = some (a, k) → (toyWin sp).HoldsK k a) :
    ∃ mem₁, Silmaril.X86.Ext.exec (.push r) σ mem n =
      .ok { σ.write .rsp (σ.read .rsp - 8#64) with rip := σ.rip + BitVec.ofNat 64 n } mem₁ := by
  obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store rfl (hw _ 8 rfl) (σ.read r)
  exact ⟨mem', by simp only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some, retire]⟩

/-- x86 progress of the toy: from RIP at one of the first three instructions of `f` (which read
no flag) or with defined modelled flags, the instruction at RIP retires (its access in the
window), and the flags are then defined or RIP at the next of those three. -/
theorem toy_progress (b sp : Word) (σ : State) (mem : Silmaril.Process.Memory)
    (i : Silmaril.X86.Ext.Instr) (n : Nat)
    (hD : Defined σ.flags ∨ σ.rip = b + 0x1d ∨ σ.rip = b + 0x1e ∨ σ.rip = b + 0x20)
    (hl : lookupI (toyTab b) σ.rip = some (i, n)) (hM : ∃ s : Store Nat, MemEnc s encFrameM mem (toyWin sp))
    (hw : ∀ a k, access i σ n = some (a, k) → (toyWin sp).HoldsK k a) (hs : (emitM (toyWin sp) i n).isSome) :
    ∃ σ₁ mem₁, Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ mem₁ ∧
      (Defined σ₁.flags ∨ σ₁.rip = b + 0x1d ∨ σ₁.rip = b + 0x1e ∨ σ₁.rip = b + 0x20) := by
  obtain ⟨s, hM⟩ := hM
  obtain ⟨code, hc⟩ := Option.isSome_iff_exists.mp hs
  rcases hD with hd | h1 | h2 | h3
  · obtain ⟨σ₁, mem₁, hx, hd₁⟩ := emitM_progress hc hM hd hw
    exact ⟨σ₁, mem₁, hx, .inl hd₁⟩
  · obtain ⟨rfl, rfl⟩ : Silmaril.X86.Ext.Instr.push .rbx = i ∧ 1 = n := by
      simpa only [h1, toyTab, lookupI, add_right_inj, add_eq_left, BitVec.reduceEq,
        ite_false, ite_true, Option.some.injEq, Prod.mk.injEq] using hl
    obtain ⟨mem₁, hx⟩ := toy_push_exec hM hw
    exact ⟨_, mem₁, hx, .inr (.inr (.inl (by simp [h1, BitVec.add_assoc])))⟩
  · obtain ⟨rfl, rfl⟩ : Silmaril.X86.Ext.Instr.push .r12 = i ∧ 2 = n := by
      simpa only [h2, toyTab, lookupI, add_right_inj, add_eq_left, BitVec.reduceEq,
        ite_false, ite_true, Option.some.injEq, Prod.mk.injEq] using hl
    obtain ⟨mem₁, hx⟩ := toy_push_exec hM hw
    exact ⟨_, mem₁, hx, .inr (.inr (.inr (by simp [h2, BitVec.add_assoc])))⟩
  · obtain ⟨rfl, rfl⟩ : Silmaril.X86.Ext.Instr.aluI8 .q .sub (.reg .rsp) 8 = i ∧ 4 = n := by
      simpa only [h3, toyTab, lookupI, add_right_inj, add_eq_left, BitVec.reduceEq,
        ite_false, ite_true, Option.some.injEq, Prod.mk.injEq] using hl
    exact ⟨_, _, rfl, .inl ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The code of the toy at `b`, outside the window, decodes to `toyTab b`. -/
theorem toy_tabAt {mem : Silmaril.Process.Memory} {b sp : Word} (hb : BytesAt mem b toyBytes)
    (hbw : b.toNat + 0x42 ≤ 2 ^ 64) (h32 : 32 ≤ sp.toNat)
    (hdisj : b.toNat + 0x42 ≤ sp.toNat - 32 ∨ sp.toNat + 8 ≤ b.toNat) :
    TabAtM mem (toyWin sp) (toyTab b) := by
  simp only [toyBytes, BytesAt, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hb
  obtain ⟨h00, h07, h0a, h0c, h0f, h13, h15, h16, h19, h1c, h1d, h1e, h20, h24, h27, h2c, h2f, h32',
    h37, h3a, h3e, h40, h41, -⟩ := hb
  have hout : ∀ (c : Word) (len : Nat), c.toNat + len ≤ 0x42 → ∀ o < len,
      ¬ (toyWin sp).Mem ((b + c).toNat + o) := by
    intro c len hc o ho hm
    have hbc : (b + c).toNat = b.toNat + c.toNat := by rw [BitVec.toNat_add]; omega
    have hsp : (sp - 32).toNat = sp.toNat - 32 := by bv_omega
    have hm' : sp.toNat - 32 ≤ b.toNat + c.toNat + o ∧ b.toNat + c.toNat + o < sp.toNat - 32 + 40 := by
      simpa only [Win.Mem, toyWin, hbc, hsp] using hm
    omega
  have hout0 : ∀ o < 7, ¬ (toyWin sp).Mem (b.toNat + o) := by
    simpa using hout 0 7 (by decide)
  show ∀ e ∈ toyTab b, _
  simp only [toyTab, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, h00, by decide, hout0⟩
  · exact ⟨_, h07, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h0a, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h0c, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h0f, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h13, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h15, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h16, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h19, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h1c, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h1d, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h1e, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h20, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h24, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h27, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h2c, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h2f, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h32', by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h37, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h3a, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h3e, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h40, by decide, hout _ _ (by decide)⟩
  · exact ⟨_, h41, by decide, hout _ _ (by decide)⟩

theorem loadN_of_readBytes {mem : Silmaril.Process.Memory} {a r : Word}
    (h : mem.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [r])) :
    Silmaril.X86.Ext.loadN mem a 8 = some r := by
  simp only [Silmaril.X86.Ext.loadN, h, Option.map_some, ← Silmaril.X86.Ext.leBytes_eight,
    Silmaril.X86.Ext.leValue_leBytes, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt r.isLt]

/-- **The contract's spec** of `f`: entry at `rip` (code at `rip - 0x1d`), the stack window, the
return address outside the code; footprint the window; `rax = sum_to(rdi) + dbl(rsi)`. -/
def toySpec : FnContract.Spec MState where
  entry s :=
    BytesAt s.memory (s.core.rip - 0x1d) toyBytes ∧ WinOK s.memory (toyWin (s.core.read .rsp)) ∧
      32 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat + 8 ≤ 2 ^ 64 ∧
      (s.core.rip - 0x1d).toNat + 0x42 ≤ 2 ^ 64 ∧
      ((s.core.rip - 0x1d).toNat + 0x42 ≤ (s.core.read .rsp).toNat - 32 ∨
        (s.core.read .rsp).toNat + 8 ≤ (s.core.rip - 0x1d).toNat) ∧
      0x42 ≤ (Open.retOf s.core s.memory - (s.core.rip - 0x1d)).toNat
  footprint s a := (toyWin (s.core.read .rsp)).Mem a
  post s t := t.core.read .rax =
    BitVec.ofNat 64 (tri (s.core.read .rdi).toNat) + 2 * s.core.read .rsi

/-- **`f` meets its System V contract on `Open9.isa`** (total correctness). -/
theorem toySpec_total : toySpec.Total Open9.isa := by
  rintro ⟨σ, mem⟩ _ habi hent
  simp only [Open9.isa] at habi hent ⊢
  obtain ⟨hb, hwin, h32, h8, hbw, hdisj, hret⟩ := hent
  set sp := σ.read .rsp with hsp
  set b := σ.rip - 0x1d with hbdef
  set ret := Open.retOf σ mem
  have hrip : σ.rip = b + 0x1d := by rw [hbdef]; simp
  have htab : TabAtM mem (toyWin sp) (toyTab b) := toy_tabAt hb hbw h32 hdisj
  -- the initial store and its first cut point
  have hE : Enc (encStoreM (H := Nat) σ mem (toyWin sp)) encFrameM σ := enc_encStoreM σ mem _
  have hM : MemEnc (encStoreM (H := Nat) σ mem (toyWin sp)) encFrameM mem (toyWin sp) :=
    memEnc_encStoreM hwin
  have hretLd : Ld (winBytes mem (toyWin sp)) 32 ret := by
    obtain ⟨B, v, hB, hv, hl⟩ := hM.load (a := sp) (by simp only [Win.Holds, toyWin]; bv_omega)
    have hBw : winBytes mem (toyWin sp) = B :=
      Option.some.inj ((wbytes_encStoreM σ mem _).symm.trans hB)
    have hvr : ret = v := Option.some.inj ((loadN_of_readBytes habi.returnAddress).symm.trans hv)
    have ho : sp.toNat - (toyWin sp).lo.toNat = 32 := by simp only [toyWin]; bv_omega
    rw [hBw, hvr, ← ho]
    exact hl
  have hJ : JT b sp ret encFrameM σ.read (5 * (σ.read .rdi).toNat + 29)
      (encStoreM (H := Nat) σ mem (toyWin sp)) :=
    jt_init (b := b) (sp := sp) (ret := ret) hE.gregs hE.2.2.1 (wbytes_encStoreM σ mem _)
      (by rw [winBytes_size]) hrip rfl hretLd
  -- the run exists
  obtain ⟨n, σe, meme, hx⟩ := xrun_existsM (supported b sp) (JT b sp ret encFrameM σ.read)
    (fun k s hk w code hw hc => by
      obtain ⟨w', hw', hm⟩ := toy_entries b sp ret σ.read h32 h8 hret k s hk
      have hww : w = w' := val_i64_inj.mp (Option.some.inj (hw.symm.trans hw'))
      subst hww
      simpa only [hc] using hm)
    (fun σ => Defined σ.flags ∨ σ.rip = b + 0x1d ∨ σ.rip = b + 0x1e ∨ σ.rip = b + 0x20)
    (toy_progress b sp) _ _ σ mem hJ hE hM (.inr (.inl hrip))
  -- its result, from the Wasm solution
  obtain ⟨hrax, hrsp, hoth, hrip'⟩ := x86_solution b sp σ σe mem meme n hwin
    ⟨hrip, rfl, h32, h8, ret, hretLd, hret⟩ hx
  have hripe : ret = σe.rip := Option.some.inj (hretLd.symm.trans hrip')
  -- it is a run of the open machine
  obtain ⟨hrun, hww⟩ := run_of_xrunM (supported b sp) hx htab
  refine ⟨⟨σe, meme⟩, ⟨n, Open9.run_of_open n hrun⟩, rfl, ⟨hripe.symm, hrsp, fun r hr => ?_⟩, hww,
    hrax⟩
  have hr' : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
    simpa only [sysv64, List.mem_cons, List.not_mem_nil, or_false] using hr
  exact hoth r (by rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- **`f` as a System V function contract** on `Open9.isa`. -/
def toyContract : FnContract Open9.isa := ⟨toySpec, toySpec_total⟩

end Silmaril.Sim.X86.Toy
