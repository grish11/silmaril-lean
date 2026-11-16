module

public import Silmaril.Sim.Reduce.Toy.Dbl.Defs
public import Silmaril.Sim.Reduce.PCalls.Thms
public import Silmaril.Sim.X86.G.Thms
public import Silmaril.Machine.X86.FnContract.Thms
public import Silmaril.Machine.X86.Open9.Thms

/-!
# The toy's `dbl`, end to end: proofs

The header is `Silmaril/Sim/Reduce/Toy/Dbl/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Toy.Dbl

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GCert Silmaril.Sim.Reduce.PCalls Silmaril.Wasm.Logic.Hoare
open Silmaril.X86 (Reg State MState Word Byte)

/-- `Val.i64` is injective. -/
theorem i64_inj {x y : BitVec 64} (h : Val.i64 x = Val.i64 y) : x = y := by cases h; rfl

/-- **The piece, solved** (every-run call rule with the step methods' contracts). -/
theorem piece : PieceStmt := by
  intro H P host
  rintro s f mi R ⟨⟨a₀, fi₀, hx₀, hf₀, hm₀, hS₀⟩, ⟨a₁, fi₁, hx₁', hf₁, hm₁, hS₁⟩, -⟩
    ⟨hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩ -
  have hE : Enc s (simFrame mi) (stateOf R w bc bz bs bo) := enc_stateOf hl hr hw hc hz hs ho
  let mem : Silmaril.Process.Memory := ⟨[], {}⟩
  show HWP P host s f (.plain (.call ⟨0⟩) :: .plain (.call ⟨1⟩) :: []) _
  refine hwp_call_step hx₀ hf₀ hS₀ ⟨hf₀, rfl, R, by rw [hm₀]; exact ⟨hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩⟩ ?_
  rintro s₁ ⟨hF₁, hp₁⟩
  obtain ⟨σ₁, hx₁, hrd₁⟩ : ∃ σ₁, Silmaril.X86.Ext.exec (.mov .q (.reg .rax) .rdi) (stateOf R w bc bz bs bo) mem 3 = .ok σ₁ mem ∧ σ₁.read = fun r => if r = .rax then R .rdi else R r := by
    refine ⟨_, by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire]; rfl, ?_⟩
    funext r; by_cases h : r = .rax <;> simp [h, stateOf] <;> rfl
  have hE₁ : Enc s₁ (simFrame mi) σ₁ := by
    rw [← hm₀]; exact hp₁ _ σ₁ mem mem (by rw [hm₀]; exact hE) hx₁
  refine hwp_call_step hx₁' (by rw [frames_funcs hF₁]; exact hf₁) hS₁
    ⟨by rw [frames_funcs hF₁]; exact hf₁, rfl, σ₁.read, by rw [hm₁]; exact hE₁.gregs⟩ ?_
  rintro s₂ ⟨-, hp₂⟩
  obtain ⟨σ₂, hx₂, hrd₂⟩ : ∃ σ₂, Silmaril.X86.Ext.exec (.alu .q .add (.reg .rax) .rax) σ₁ mem 3 = .ok σ₂ mem ∧
      σ₂.read = fun r => if r = .rax then σ₁.read .rax + σ₁.read .rax else σ₁.read r := by
    refine ⟨_, by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.aluStep,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.AluOp.flagsN]; rfl, ?_⟩
    funext r; by_cases h : r = .rax <;> simp [h]; rfl
  have hE₂ : Enc s₂ (simFrame mi) σ₂ := by
    rw [← hm₁]; exact hp₂ σ₁ σ₂ mem mem (by rw [hm₁]; exact hE₁) hx₂
  have key : ∀ R' : Reg → BitVec 64, (∀ r, gval s₂ (simFrame mi) (.reg r) = some (Val.i64 (R' r))) →
      DblPost R R' := by
    intro R' hR'
    have hR'r : ∀ r, R' r = σ₂.read r := fun r =>
      i64_inj (Option.some.inj ((hR' r).symm.trans (hE₂.2.1 r)))
    refine ⟨?_, fun r hr => ?_⟩
    · rw [hR'r, hrd₂, hrd₁]; simp
    · rw [hR'r, hrd₂, hrd₁]; simp [hr]
  simpa [vals] using HWP.of_vals (P := P) (host := host) (vs := []) (s := s₂) (f := f)
    (Q := fun s' _ o => o = .normal [] ∧ ∀ R' : Reg → BitVec 64,
      (∀ r, gval s' (simFrame mi) (.reg r) = some (Val.i64 (R' r))) → DblPost R R') ⟨rfl, key⟩

/-- The instance lays the globals out at `0..22`. -/
theorem dbl_globals : dblMI.globals = List.range 23 := by decide +kernel

/-- **Translation validity and the method pieces** for the instantiated module: the calls reach
the step methods `emit i len` of the instructions of `dblProg`. -/
theorem dbl_fns : StepFns dblStore (Frame.forCall dblMI [] []) dblMI dblProg dblCalls := by
  have hlen : dblStore.funcs.length = 3 := rfl
  obtain ⟨f₀, f₁, f₂, hf⟩ : ∃ f₀ f₁ f₂, dblStore.funcs = [f₀, f₁, f₂] := by
    match h : dblStore.funcs, hlen with
    | [f₀, f₁, f₂], _ => exact ⟨f₀, f₁, f₂, rfl⟩
  have hc : dblStore.funcs.map FuncInst.code =
      [.wasm dblModule.funcs[0], .wasm dblModule.funcs[1], .wasm dblModule.funcs[2]] := rfl
  have hm : dblStore.funcs.map FuncInst.module = [dblMI, dblMI, dblMI] := rfl
  have ht : dblStore.funcs.map (fun fi => Silmaril.Wasm.Game.FnType.ofDefType? fi.type) =
      [some ⟨[], []⟩, some ⟨[], []⟩, some ⟨[], []⟩] := by decide +kernel
  have hmf : dblMI.funcs = [0, 1, 2] := rfl
  rw [hf] at hc hm ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc hm ht
  refine ⟨⟨0, f₀, dblModule.funcs[0], by show dblMI.funcs[_]? = _; rw [hmf]; rfl, by rw [hf]; rfl, hm.1, hc.1, ht.1, rfl, rfl⟩,
    ⟨1, f₁, dblModule.funcs[1], by show dblMI.funcs[_]? = _; rw [hmf]; rfl, by rw [hf]; rfl, hm.2.1, hc.2.1, ht.2.1, rfl, rfl⟩, trivial⟩

/-- **P-calls soundness, instantiated**: the piece solves the x86 problem (method pieces and
translation validity are `dbl_fns`: the instantiated module's step methods are `emit i len`). -/
theorem x86_of_piece (h : PieceStmt) : X86Stmt :=
  xproblem_of_piece (H := Nat) (h (H := Nat) Silmaril.Wasm.Logic.Hoare.detP (fun _ _ _ _ => False)) dbl_globals
    dbl_fns


/-- The body always retires. -/
theorem dblProg_runs (σ : State) (mem : Silmaril.Process.Memory) :
    ∃ σ', runExt dblProg σ mem = some (σ', mem) := by
  simp [runExt, dblProg, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.aluStep,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.AluOp.flagsN]

/-- The bytes decode to the body and `ret`. -/
theorem dblBytes_decode : ∀ (k : Nat) (_h₁ : k < (dblProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)]).length)
    (h₂ : k < dblBytes.length),
    Silmaril.X86.Ext.decode dblBytes[k] = some (dblProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k] ∧
      (dblProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k].2 = dblBytes[k].length := by
  decide

/-- `dbl` on the bytes: returns to `exit` with `rax = rdi + rdi`, the other registers but `rsp`
and the memory unchanged. -/
theorem dbl_returns (hx86 : X86Stmt) (m : MState) (exit : Word) (hb : BytesAt m.memory m.core.rip dblBytes)
    {stack : List Byte} (hs : m.memory.readBytes (m.core.read .rsp).toNat 8 = some stack)
    (hw : Silmaril.X86.wordOfBytes? stack = some exit) :
    ∃ final : MState, Silmaril.X86.Ext.Returns exit m final ∧ final.core.rip = exit ∧
      final.core.read .rax = m.core.read .rdi + m.core.read .rdi ∧
      final.core.read .rsp = m.core.read .rsp + 8#64 ∧ final.memory = m.memory ∧
      ∀ r, r ≠ .rax → r ≠ .rsp → final.core.read r = m.core.read r := by
  obtain ⟨σ, mem⟩ := m
  have hcode := codeAt_of_bytesAt (p := dblProg ++ [(.ret, 1)]) rfl dblBytes_decode hb
  obtain ⟨hbody, hret, -⟩ := codeAt_append hcode
  obtain ⟨σ', hx⟩ := dblProg_runs σ mem
  obtain ⟨hdbl, hframe⟩ := hx86 σ σ' mem mem trivial hx
  obtain ⟨code, hc⟩ : ∃ code, emitProg dblProg = some code := ⟨_, rfl⟩
  obtain ⟨hrun, hrip⟩ := run_of_runExt hc exit hbody hx
  rw [← hrip] at hret
  have hrsp : σ'.read .rsp = σ.read .rsp := hframe .rsp (by decide)
  have hpop : Silmaril.X86.popWord σ' mem = some (exit, σ'.write .rsp (σ'.read .rsp + 8#64)) := by
    simp only [Silmaril.X86.popWord, hrsp]
    simp [hs, hw]
  refine ⟨⟨{ σ'.write .rsp (σ'.read .rsp + 8#64) with rip := exit }, mem⟩,
    ⟨2, ⟨σ', mem⟩, hrun, ?_⟩, rfl, ?_, ?_, rfl, fun r h₁ h₂ => ?_⟩
  · simp only [Silmaril.X86.Ext.step, hret, Silmaril.X86.Ext.exec, hpop]
    simp
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rax = _
    rw [State.read_write_other σ' .rsp .rax _ (by decide)]
    exact hdbl
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read r = _
    rw [State.read_write_other σ' .rsp r _ h₂]
    exact hframe r h₁

open Silmaril.Machine.X86 in
/-- **The ISA goal from the x86 problem**: decoding the bytes (`decide`), the `ret`, and the
System V contract on the open machine (`total_of_ext_returns`, `Spec.Total.toOpen9`). -/
theorem isa_of_x86 (hx86 : X86Stmt) : Silmaril.Sim.Reduce.Toy.isaGoal .dbl := by
  intro base
  refine FnContract.Spec.Total.toOpen9 (FnContract.total_of_ext_returns _ fun m ha he => ?_)
  obtain ⟨hload, hrip⟩ := he
  have hb : BytesAt m.memory m.core.rip dblBytes := by
    have e₁ : base + BitVec.ofNat 64 16 + BitVec.ofNat 64 3 = base + BitVec.ofNat 64 19 := by
      rw [BitVec.add_assoc]; rfl
    have e₂ : base + BitVec.ofNat 64 19 + BitVec.ofNat 64 3 = base + BitVec.ofNat 64 22 := by
      rw [BitVec.add_assoc]; rfl
    rw [hrip]
    refine ⟨?_, ?_, ?_, trivial⟩
    · show m.memory.fetchBytes (base + BitVec.ofNat 64 16).toNat 3 = _
      rw [hload.toNat_add (offset := 16) (by decide), hload.fetchBytes_sub (by decide) (by decide)]; rfl
    · show m.memory.fetchBytes (base + BitVec.ofNat 64 16 + BitVec.ofNat 64 3).toNat 3 = _
      rw [e₁, hload.toNat_add (offset := 19) (by decide), hload.fetchBytes_sub (by decide) (by decide)]; rfl
    · show m.memory.fetchBytes (base + BitVec.ofNat 64 16 + BitVec.ofNat 64 3 + BitVec.ofNat 64 3).toNat 1 = _
      rw [e₁, e₂, hload.toNat_add (offset := 22) (by decide), hload.fetchBytes_sub (by decide) (by decide)]; rfl
  obtain ⟨fin, hret, -, hrax, hrsp, hmem, hoth⟩ :=
    dbl_returns hx86 m _ hb ha.returnAddress (Silmaril.X86.wordOfBytes?_encodeWords _)
  refine ⟨fin, hret, hrsp, fun r hr => hoth r ?_ ?_, by rw [hmem]; exact Silmaril.Process.Memory.WritesWithin.refl _ _, hrax⟩ <;>
    · simp [Silmaril.X86.sysv64] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The toy ISA goal for `dbl`, solved** through the P-calls Wasm piece. -/
theorem isa_dbl : Silmaril.Sim.Reduce.Toy.isaGoal .dbl := isa_of_x86 (x86_of_piece piece)

end Silmaril.Sim.Reduce.Toy.Dbl
