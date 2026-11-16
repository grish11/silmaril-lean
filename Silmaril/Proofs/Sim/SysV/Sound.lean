module

public import Silmaril.Proofs.Sim.SysV.Entry
public import Silmaril.Proofs.Sim.SysV.Wrap
public import Silmaril.Sim.Reduce.Defs
public import Silmaril.Sim.Institution.Defs

/-!
# Soundness of the System V wrapper over the G simulator, and the reduction

* `runExt_mem`: translated bodies do not touch memory.
* **`wrapper_exec`**: from a store encoding the caller's registers and a frame holding the
  arguments, the wrapper code evaluates (deterministically) to `[status, rax]` with
  `status = statusOf (entry registers) (final registers)`, for every retiring body.
* `returns_of_body`: on the `Silmaril.X86.Ext` machine, a retiring body followed by `ret`, with
  the sentinel at the final `[rsp]`, returns to the sentinel (`Ext.Returns`).
* **`wrapper_sound`**: if the wrapper returns status `0` and `r`, the set-up entry state meets
  `AbiEntry` and the function returns to the sentinel (first return) in a state meeting
  `AbiReturn` with `rax = r`.
* **`xgoal_of_wgoal`**: `WGoal → XGoal` (the Wasm problem solves the x86 problem); `reduction`,
  `instReduction`, `decomp`: the same as edges of `Silmaril.Sim.Reduce` and
  `Silmaril.Sim.Institution`.
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec_append)
open Silmaril.Wasm.Logic.Hoare (HWP)
open Silmaril.X86 (Reg State MState Word)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Sim.X86.G
open Silmaril.Machine.X86.FnContract (AbiEntry AbiReturn)

variable {H : Type}

theorem runExt_mem {p : XProg} {code : List Instr} (hc : emitProg p = some code) {σ σ' : State}
    {m m' : Memory} (hx : runExt p σ m = some (σ', m')) : m' = m :=
  (emitProg_sound (s := encStore (H := Unit) σ) hc (enc_encStore σ) hx).1

/-- **The wrapper's evaluation.** -/
theorem wrapper_exec {p : XProg} {code : List Instr} (hc : emitProg p = some code)
    {s : Store H} {f : Frame} {σ : State} (hE : Enc s f σ) {d : SysVCall} (hk : d.intArgs.length ≤ 6)
    (hL : ArgLocals f d) {σ' : State} {mem mem' : Memory}
    (hx : runExt p (entryCore d σ) mem = some (σ', mem')) :
    ∃ s' f', exec s f [] (wrapperCode d.stackArgs.length code) =
      some (s', f', [Val.i64 (statusOf (entryCore d σ).read σ'.read), Val.i64 (σ'.read .rax)]) ∧
      Enc s' f' σ' := by
  obtain ⟨s₁, f₁, hp, -, hE₁, -, hS⟩ := prologue_exec hE hk hL
  obtain ⟨-, s₂, hb, hE₂, -⟩ := emitProg_sound hc hE₁ hx
  refine ⟨s₂, f₁, ?_, hE₂⟩
  rw [wrapperCode, exec_append, exec_append, hp]
  simp only
  rw [hb]
  exact epilogue_exec hE₂ hS

/-- A retiring body followed by `ret`, with the sentinel at the final `[rsp]`, returns. -/
theorem returns_of_body {p : XProg} {code : List Instr} (hc : emitProg p = some code) (e : MState)
    (hcode : CodeAt e.memory e.core.rip (p ++ [(.ret, 1)])) {σ' : State} {m' : Memory}
    (hx : runExt p e.core e.memory = some (σ', m'))
    (hret : e.memory.readBytes (σ'.read .rsp).toNat 8 = some (encodeWords [SENTINEL])) :
    Silmaril.X86.Ext.Returns SENTINEL e
      ⟨{ σ'.write .rsp (σ'.read .rsp + 8#64) with rip := SENTINEL }, e.memory⟩ := by
  obtain ⟨σ, mem⟩ := e
  obtain ⟨hbody, hretc, -⟩ := codeAt_append hcode
  have hm := runExt_mem hc hx
  subst hm
  obtain ⟨hrun, hrip⟩ := run_of_runExt hc SENTINEL hbody hx
  rw [← hrip] at hretc
  have hpop : Silmaril.X86.popWord σ' m' = some (SENTINEL, σ'.write .rsp (σ'.read .rsp + 8#64)) :=
    Silmaril.X86.popWord_of_readBytes hret
  refine ⟨p.length, ⟨σ', m'⟩, hrun, ?_⟩
  simp only [Silmaril.X86.Ext.step, hretc, Silmaril.X86.Ext.exec, hpop]
  simp

theorem entryCore_rip (d : SysVCall) (σ : State) : (entryCore d σ).rip = d.target := rfl

theorem setArgs_read_cs (as : List Word) (σ : State) (r : Reg) (h : r ∉ Silmaril.X86.sysv64.intArgRegs) :
    (setArgs as Silmaril.X86.sysv64.intArgRegs σ).read r = σ.read r :=
  setArgs_read_other _ _ _ _ h

/-- **Soundness of the wrapper.** If the wrapper code, run from a store encoding the caller's
registers with the arguments in its frame, returns status `0` and `r`, then the entry state set
up from the descriptor meets `AbiEntry`, and the function returns to the sentinel (the first
`ret` to it) in a state meeting `AbiReturn` with `rax = r`. -/
theorem wrapper_sound {p : XProg} {code : List Instr} (hc : emitProg p = some code)
    {d : SysVCall} (hd : d.Valid) {m e : MState} (hsetup : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8)
    (hcode : CodeAt e.memory d.target (p ++ [(.ret, 1)])) {σ' : State} {m' : Memory}
    (hx : runExt p e.core e.memory = some (σ', m'))
    {s : Store H} {f : Frame} (hE : Enc s f m.core) (hL : ArgLocals f d)
    {s' : Store H} {f' : Frame} {r st : Word}
    (hw : exec s f [] (wrapperCode d.stackArgs.length code) = some (s', f', [Val.i64 st, Val.i64 r]))
    (hst : st = 0) :
    AbiEntry e.core e.memory ∧ ∃ final : MState, Silmaril.X86.Ext.Returns SENTINEL e final ∧
      AbiReturn e.core e.memory final.core ∧ final.core.read .rax = r := by
  have hcore : e.core = entryCore d m.core := setup_core hsetup
  have hxe : runExt p (entryCore d m.core) e.memory = some (σ', m') := by rw [← hcore]; exact hx
  obtain ⟨s₂, f₂, he, -⟩ := wrapper_exec hc hE hd.1 hL hxe
  have hv : s' = s₂ ∧ f' = f₂ ∧ st = statusOf (entryCore d m.core).read σ'.read ∧
      r = σ'.read .rax := by
    simpa only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, val_i64_inj, and_true]
      using hw.symm.trans he
  have hst₀ : statusOf (entryCore d m.core).read σ'.read = 0 := hv.2.2.1.symm.trans hst
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := statusOf_eq_zero hst₀
  have hrsp : σ'.read .rsp = e.core.read .rsp := by rw [hsp, hcore]
  have hret : e.memory.readBytes (σ'.read .rsp).toNat 8 = some (encodeWords [SENTINEL]) := by
    rw [hrsp, hcore, entryCore_rsp]; exact setup_ret hsetup hr
  have hcode' : CodeAt e.memory e.core.rip (p ++ [(.ret, 1)]) := by
    rw [hcore, entryCore_rip]; exact hcode
  refine ⟨setup_abiEntry hsetup hr, _, returns_of_body hc e hcode' hx hret, ⟨?_, ?_, ?_⟩, ?_⟩
  · show SENTINEL = _
    rw [setup_retOf hsetup hr]
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]
  · intro q hq
    show (σ'.write .rsp (σ'.read .rsp + 8#64)).read q = e.core.read q
    have hq' : q = .rbx ∨ q = .rbp ∨ q = .r12 ∨ q = .r13 ∨ q = .r14 ∨ q = .r15 := by
      simpa only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
        using hq
    rw [State.read_write_other _ _ _ _ (by rintro rfl; revert hq; decide), hcore]
    rcases hq' with h | h | h | h | h | h <;> rw [h] <;> assumption
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rax = r
    rw [State.read_write_other _ _ _ _ (by decide)]
    exact hv.2.2.2.symm

/-! ## The reduction -/

/-- The frame of a call: the arguments and target as parameters, eight more locals. -/
def argFrame (d : SysVCall) : Frame :=
  { encFrame with
    locals := (d.regArgs ++ [d.target] ++ List.replicate 8 0).map fun w => some (Val.i64 w) }

theorem argFrame_getElem? (d : SysVCall) (hk : d.intArgs.length ≤ 6) (i : Nat) (hi : i < 15) :
    (argFrame d).locals[i]? =
      some (some (Val.i64 ((d.regArgs ++ [d.target] ++ List.replicate 8 0)[i]'(by
        simp [regArgs_length' d hk]; omega)))) := by
  simp only [argFrame, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp [regArgs_length' d hk]; omega)]
  rfl

theorem argLocals_argFrame (d : SysVCall) (hk : d.intArgs.length ≤ 6) : ArgLocals (argFrame d) d := by
  have hl := regArgs_length' d hk
  refine ⟨by simp [argFrame, hl], fun i => ?_, ?_, fun i hi => ⟨_, argFrame_getElem? d hk i hi⟩⟩
  · rw [argFrame_getElem? d hk i.val (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hl]; exact i.isLt)]
    simp only [Option.getD_some, List.append_assoc]
    rw [List.getElem_append_left]
  · rw [argFrame_getElem? d hk 6 (by omega)]
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp [hl]

/-- **The reduction**: a solution of the Wasm problem (at any profile and host relation) is a
solution of the x86 problem. -/
theorem xgoal_of_wgoal {P : Profile} {host : HostSemantics H} {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) {n : Nat} {Pre : SysVCall → Prop} {Post : SysVCall → Word → Prop}
    (hW : WGoal P host code n Pre Post) : XGoal p n Pre Post := by
  intro d m e hd hn hpre hsetup hr hcode ⟨σ', m', hx⟩
  subst hn
  have hE : Enc (encStore (H := H) m.core) (argFrame d) m.core :=
    enc_frame (f' := argFrame d) (f := encFrame) rfl (enc_encStore m.core)
  have hL := argLocals_argFrame d hd.1
  have hx' := hx
  rw [setup_core hsetup] at hx'
  obtain ⟨s', f', he, -⟩ := wrapper_exec hc hE hd.1 hL hx'
  have hs := Silmaril.Wasm.Logic.Core.exec_sound (P := P) (host := host) (rest := []) he
  simp only [List.reverse_nil, List.append_nil] at hs
  have hq := Silmaril.Wasm.Logic.Hoare.HWP.sound_vals
    (vs := [Val.i64 (σ'.read .rax), Val.i64 (statusOf (entryCore d m.core).read σ'.read)])
    (hW _ _ m.core.read d hd rfl hpre hE.gregs hL) (by simpa [vals] using hs)
  obtain ⟨r, st, ho, hst, hpost⟩ := hq
  simp only [Silmaril.Wasm.Logic.Core.Outcome.normal.injEq, List.cons.injEq, val_i64_inj, and_true] at ho
  obtain ⟨rfl, rfl⟩ := ho
  obtain ⟨habi, final, hret, hres, hrax⟩ := wrapper_sound hc hd hsetup hr hcode hx hE hL he hst
  exact ⟨habi, final, hret, hres, hrax ▸ hpost⟩

/-- The reduction as a `Silmaril.Sim.Reduce.Reduction` edge (x86 problem ← Wasm problem). -/
def reduction (P : Profile) (host : HostSemantics H) {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) (n : Nat) (Pre : SysVCall → Prop) (Post : SysVCall → Word → Prop) :
    Silmaril.Sim.Reduce.Reduction where
  src := XGoal p n Pre Post
  tgt := WGoal P host code n Pre Post
  sound := xgoal_of_wgoal hc

/-- Derived from `reduction`: the same single step (subgoal the Wasm problem `WGoal`) as a
goal-indexed `Silmaril.Sim.Institution.Reduction`. The canonical reduction record is
`Silmaril.Sim.Reduce.Decomp` (`decomp` in `Silmaril.Proofs.Sim.SysV.Edge`); this view is kept for
institution-level composition. -/
def instReduction (P : Profile) (host : HostSemantics H) {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) (n : Nat) (Pre : SysVCall → Prop) (Post : SysVCall → Word → Prop) :
    Silmaril.Sim.Institution.Reduction (XGoal p n Pre Post) where
  subgoals := [WGoal P host code n Pre Post]
  sound h := xgoal_of_wgoal hc (h _ (List.mem_singleton_self _))

@[deprecated xgoal_of_wgoal (since := "2026-11-10")] alias reduce := xgoal_of_wgoal

end Silmaril.Sim.SysV
