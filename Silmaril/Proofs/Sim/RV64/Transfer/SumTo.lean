module

public import Silmaril.Proofs.Sim.RV64.Transfer.Generic
public import Silmaril.Sim.RV64.Cfg.Thms
public import Silmaril.WasmSpec.Rv64SumTo.Defs
public import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `sum_to`: a loop, from its Wasm problem to the RV64 problem

Cut point `0x11244` (the plan's loop header). The blocks `T0` (entry to the cut) and `T1` (from
the cut) are computed by `cfgSym` and checked by `decide` (`sym0`, `sym1`), sound by
`Silmaril.Sim.RV64.Cfg.reach_block`. **Translation validation** (`tv`): every run of the Wasm body
that returns `v` corresponds to an `Ext` run returning `v`; it is the generator's condition
`wpc` with the **simulation invariant** at the Wasm loop: "the RV64 machine reaches the cut point
with `a0`, `t0` equal to the Wasm locals" (`Reach`). **Termination** comes from the Wasm problem
(`Spec` is total correctness: some terminating run), so `isa : Spec → ISA` gives a terminating
RV64 run.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Transfer.SumTo

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym Silmaril.Sim.RV64.Cfg Silmaril.Sim.RV64.Transfer Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.VC
open Silmaril.WasmSpec.Rv64SumTo (func program Pre Post Spec)

def words : List (BitVec 32) :=
  [0x00000293, 0x00050863, 0x00a282b3, 0xfff50513, 0xff5ff06f, 0x00028513, 0x00008067]

def cuts : List W64 := [0x11244#64]

def T0 : Tree2 := (Tree2.leaf (Leaf.goto 0x0000000000011244#64 [E.const 0x0000000000000000#64, E.var 0x01#5, E.var 0x02#5, E.var 0x03#5, E.var 0x04#5, E.bin (Bin.add) (E.const 0x0000000000000000#64) (E.const 0x0000000000000000#64), E.var 0x06#5, E.var 0x07#5, E.var 0x08#5, E.var 0x09#5, E.var 0x0a#5, E.var 0x0b#5, E.var 0x0c#5, E.var 0x0d#5, E.var 0x0e#5, E.var 0x0f#5, E.var 0x10#5, E.var 0x11#5, E.var 0x12#5, E.var 0x13#5, E.var 0x14#5, E.var 0x15#5, E.var 0x16#5, E.var 0x17#5, E.var 0x18#5, E.var 0x19#5, E.var 0x1a#5, E.var 0x1b#5, E.var 0x1c#5, E.var 0x1d#5, E.var 0x1e#5, E.var 0x1f#5]))

def T1 : Tree2 := (Tree2.br (BranchOp.eq) (E.var 0x0a#5) (E.const 0x0000000000000000#64) (Tree2.leaf (Leaf.ret (E.bin (Bin.add) (E.var 0x05#5) (E.const 0x0000000000000000#64)))) (Tree2.leaf (Leaf.goto 0x0000000000011244#64 [E.const 0x0000000000000000#64, E.var 0x01#5, E.var 0x02#5, E.var 0x03#5, E.var 0x04#5, E.bin (Bin.add) (E.var 0x05#5) (E.var 0x0a#5), E.var 0x06#5, E.var 0x07#5, E.var 0x08#5, E.var 0x09#5, E.bin (Bin.add) (E.var 0x0a#5) (E.const 0xffffffffffffffff#64), E.var 0x0b#5, E.var 0x0c#5, E.var 0x0d#5, E.var 0x0e#5, E.var 0x0f#5, E.var 0x10#5, E.var 0x11#5, E.var 0x12#5, E.var 0x13#5, E.var 0x14#5, E.var 0x15#5, E.var 0x16#5, E.var 0x17#5, E.var 0x18#5, E.var 0x19#5, E.var 0x1a#5, E.var 0x1b#5, E.var 0x1c#5, E.var 0x1d#5, E.var 0x1e#5, E.var 0x1f#5])))

set_option maxRecDepth 10000 in
theorem sym0 : cfgSym (codeAt 0x11240 words) cuts 10 true 0x11240#64 regs0 = some T0 := by decide

set_option maxRecDepth 10000 in
theorem sym1 : cfgSym (codeAt 0x11240 words) cuts 10 true 0x11244#64 regs0 = some T1 := by decide

/-- The simulation invariant at the Wasm loop. -/
def simInv {H : Type} (m₀ : MState) (s₀ : Store H) (mi : ModuleInst) : Invs H :=
  fun _ s f a => s = s₀ ∧ a = [] ∧ ∃ σ : Reg → W64, Reach m₀ 0x11244#64 σ ∧
    f = ⟨[some (.i64 (σ 10#5)), some (.i64 (σ 5#5))], mi⟩

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- **Translation validation**, as the generator's condition with the simulation invariant. -/
theorem tv_body (m₀ : MState) (hcode : ∀ p w, codeAt 0x11240 words p = some w → fetch m₀.memory p = some w)
    (hpc : m₀.core.pc = 0x11240#64) (hra : (m₀.core.read 1#5).toNat % 4 = 0)
    {H : Type} (s : Store H) (mi : ModuleInst) (R : Store H → Silmaril.Wasm.Logic.Core.Outcome → Prop)
    (hR : ∀ v, Returns m₀ v → R s (.normal [.i64 v])) :
    wpc (simInv m₀ s mi) 0 func.body (fnPost 1 R) s
      (Frame.forCall mi [.i64 (m₀.core.read 10#5)] func.locals) [] := by
  have h0 := reach_block hcode hra sym0 (hpc ▸ reach_entry m₀)
  simp [T0, Tree2.run, BlockOut] at h0
  simp [func, program, wpc, ctl, enterVC, labelQ, loopQ, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
    Frame.local?, Frame.setLocal, Frame.forCall, ModuleInst.blockType?, Idx.toNat, Val.i64,
    Val.i32, simInv, defaultVal_i64, intRelOp_i64_eq, bool32, fnPost]
  refine ⟨⟨_, h0, ?_, ?_⟩, ?_⟩
  · simp [Leaf.vals, E.eval]
  · simp [Leaf.vals, E.eval, Bin.eval]
  rintro s' f' rfl σ hσ rfl -
  have h1 := reach_block hcode hra sym1 hσ
  simp [T1, Tree2.run, BlockOut, E.eval, BranchOp.eval] at h1
  simp [Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal, Val.i64, intRelOp_i64_eq, bool32]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [ite_eq_left hz] at h1
    simpa [Bin.eval, Val.i64] using hR _ h1
  · rw [ite_eq_right hz] at h1
    exact ⟨_, h1, by simp [Leaf.vals, E.eval, Bin.eval], by simp [Leaf.vals, E.eval, Bin.eval]⟩

/-- The instantiated module. -/
def store : Store Nat := Silmaril.WasmSpec.Rv64SumTo.store

/-- The type `[i64] → [i64]`. -/
def ty : FnType := ⟨[.num (.int .i64)], [.num (.int .i64)]⟩

theorem funcs : ∃ fi : FuncInst Nat, store.funcs[0]? = some fi ∧ fi.code = .wasm func ∧
    FnType.ofDefType? fi.type = some ty := by
  have hlen : store.funcs.length = 1 := by decide +kernel
  obtain ⟨fi, hf⟩ : ∃ fi, store.funcs = [fi] := by
    match h : store.funcs, hlen with
    | [fi], _ => exact ⟨fi, rfl⟩
  have hc : store.funcs.map FuncInst.code = [.wasm func] := rfl
  have ht : store.funcs.map (fun fi => FnType.ofDefType? fi.type) = [some ty] := by
    decide +kernel
  rw [hf] at hc ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht
  exact ⟨fi, by rw [hf]; rfl, hc, ht⟩

def PreL : List W64 → Prop
  | [a0] => Pre a0
  | _ => False

def PostL : List W64 → W64 → Prop
  | [a0], r => Post a0 r
  | _, _ => False

/-- **The RV64 problem** of `sum_to` (contract + leaf ABI, total: the machine returns). -/
def ISA : Prop := FnISAP 0x11240 words [10#5] PreL PostL

private theorem i64_of_normal {v w : BitVec 64}
    (h : Silmaril.Wasm.Logic.Core.Outcome.normal [Val.i64 v] = .normal [Val.i64 w]) : v = w := by
  cases h; rfl

/-- **The transfer** (with termination from the Wasm problem). -/
theorem isa (hS : Spec) : ISA := by
  intro m hpc hc hra hpre
  obtain ⟨fi, hf, hcode, ht⟩ := funcs
  have he : Silmaril.Wasm.Validation.Expand fi.type ty.toComp := FnType.expand_of_ofDefType? ht
  have hcode' : ∀ p w, codeAt 0x11240 words p = some w → fetch m.memory p = some w :=
    code_of_codeAt hc (by decide)
  -- a terminating Wasm run satisfying the contract (the Wasm problem)
  obtain ⟨s', res, hs, -, x, hres, hp⟩ := Silmaril.Wasm.Logic.Core.funcSpec_invoke_of_body
    (P := Profile.spec) (host := fun _ _ _ _ => False) (a := 0)
    (Pre := fun s args => s = store ∧ args = [.i64 (m.core.read 10#5)])
    (Post := fun s _ s' res => s' = s ∧ ∃ x, res = [.i64 x] ∧ Post (m.core.read 10#5) x)
    (fun _ _ h => by rw [h.1]; exact hf) hcode he (fun _ _ h => by rw [h.2]; rfl)
    (fun s args h => by
      obtain ⟨rfl, rfl⟩ := h
      exact hS _ hpre fi hf Profile.spec (fun _ _ _ _ => False)) ⟨rfl, rfl⟩
  -- translation validation: every returning run is an RV64 return
  let S : Silmaril.Wasm.Logic.Hoare.FSpec Nat :=
    { pre := fun s args => s.funcs[0]? = some fi ∧ args = [.i64 (m.core.read 10#5)]
      post := fun _ _ _ o => ∀ v, o = .normal [.i64 v] → Returns m v }
  have hV : Silmaril.Wasm.Logic.Hoare.FSpecValid Profile.spec (fun _ _ _ _ => False) 0 S := by
    refine FSpecValid.of_fnPost (fun _ _ h => h.1) hcode he (fun _ _ h => by rw [h.2]; rfl) ?_
    rintro s args ⟨-, hargs⟩
    rw [hargs, show (Validation.Ty.ofList (List.map ScalarType.toC ty.results)).length = 1 from rfl]
    simpa [vals] using wpc_sound (P := Profile.spec) (host := fun _ _ _ _ => False)
      (simInv m s fi.module) 0 func.body _ s _ [] (tv_body m hcode' hpc hra s fi.module
        (S.post s [.i64 (m.core.read 10#5)]) fun v hv w hw => i64_of_normal hw ▸ hv)
  have hret : Returns m x := Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals hV
    (show S.pre store _ from ⟨hf, rfl⟩) hs x (by rw [hres])
  obtain ⟨k, m', hrun, h1, h2, h3⟩ := hret
  exact ⟨k, m', hrun, h1, h3, by simpa [PostL, h2] using hp⟩

/-! ## The Wasm problem, with the plan's invariant and the measure `a0` -/

section Spec

open Silmaril.Wasm.Logic.Core

/-- `0 + 1 + ⋯ + x` modulo `2⁶⁴`. -/
def tri64 (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat * (x.toNat + 1) / 2)

theorem tri64_zero : tri64 0 = 0 := rfl

theorem tri64_step {a : BitVec 64} (ha : a ≠ 0) : tri64 a = tri64 (a + 0xffffffffffffffff#64) + a := by
  have h0 : a.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using ha
  obtain ⟨k, hk⟩ : ∃ k, a.toNat = k + 1 := ⟨a.toNat - 1, by omega⟩
  have e : (a + 0xffffffffffffffff#64).toNat = k := by
    rw [BitVec.toNat_add]; have := a.isLt; simp; omega
  apply BitVec.eq_of_toNat_eq
  simp only [tri64, BitVec.toNat_add, BitVec.toNat_ofNat, e, hk]
  have h2 : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
    have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by decide)]
  rw [h2]; omega

theorem dec_lt {a : BitVec 64} (ha : a ≠ 0) : (a + 0xffffffffffffffff#64).toNat < a.toNat := by
  have h0 : a.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using ha
  rw [BitVec.toNat_add]; have := a.isLt; simp; omega

/-- The loop body, quoted. -/
def loopBody : List Silmaril.Wasm.Instr :=
  [.localGet ⟨0⟩, .intConst .i64 0, .intRelOp .i64 .eq,
   .if_ .empty [.localGet ⟨1⟩, .intConst .i64 0, .intBinOp .i64 .add, .localSet ⟨0⟩,
      .localGet ⟨0⟩, .return_]
    [.localGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i64 .add, .localSet ⟨1⟩, .localGet ⟨0⟩,
      .intConst .i64 0xffffffffffffffff, .intBinOp .i64 .add, .localSet ⟨0⟩, .br ⟨1⟩]]

set_option maxRecDepth 10000 in
theorem body_eq : func.body = [.intConst .i64 0, .intConst .i64 0, .intBinOp .i64 .add,
    .localSet ⟨1⟩, .loop .empty loopBody, .unreachable] := rfl

theorem locals_eq : func.locals = [.num (.int .i64)] := rfl

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The plan's loop invariant (`t0 + tri a0 = tri a0₀`), measure `a0`. -/
def Inv (s₀ : Store H) (m : ModuleInst) (a₀ : BitVec 64) :
    Nat → Store H → Frame → List Val → Prop := fun k s f vs =>
  s = s₀ ∧ vs = [] ∧ ∃ a t : BitVec 64,
    f = ⟨[some (.i64 a), some (.i64 t)], m⟩ ∧ k = a.toNat ∧ t + tri64 a = tri64 a₀

private theorem inv_dec {a t a₀ : BitVec 64} (ha : a ≠ 0) (hinv : t + tri64 a = tri64 a₀) :
    t + a + tri64 (a + 18446744073709551615#64) = tri64 a₀ := by
  rw [← hinv, tri64_step ha]; bv_omega

set_option maxRecDepth 10000 in
theorem inv_body {s₀ : Store H} {m : ModuleInst} {a₀ : BitVec 64} {k : Nat} {s : Store H}
    {f : Frame} {vs : List Val} (h : Inv s₀ m a₀ k s f vs) :
    WP P host s f (vals vs ++ expression loopBody)
      (loopPost 0 (Inv s₀ m a₀) k (seqPost P host (expression [.unreachable])
        (funcPost P host 1 fun s' r => s' = s₀ ∧ ∃ r_a0, r = [.i64 r_a0] ∧ Post a₀ r_a0))) := by
  obtain ⟨rfl, rfl, a, t, rfl, rfl, hinv⟩ : s = s₀ ∧ vs = [] ∧ ∃ a t : BitVec 64,
      f = ⟨[some (.i64 a), some (.i64 t)], m⟩ ∧ k = a.toNat ∧ t + tri64 a = tri64 a₀ := h
  show WP P host s _ (vals [] ++ expression [.localGet ⟨0⟩, .intConst .i64 0, .intRelOp .i64 .eq] ++
    .plain (.if_ .empty _ _) :: []) _
  wasm_step [Idx.toNat, Fin.val_zero, Silmaril.Wasm.Logic.VC.intRelOp_i64_eq]
  refine wp_if_bool32_cons (vs := []) ?_
  by_cases ha : a = 0
  · rw [ha]
    refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
    show WP P host s _ (vals [] ++ expression [.localGet ⟨1⟩, .intConst .i64 0, .intBinOp .i64 .add,
      .localSet ⟨0⟩, .localGet ⟨0⟩] ++ .plain .return_ :: []) _
    wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one]
    refine wp_return ⟨[], _, rfl, rfl, rfl, _, rfl, ?_⟩
    have hinv0 : t + tri64 0 = tri64 a₀ := ha ▸ hinv
    simpa [Silmaril.WasmSpec.Rv64SumTo.Post, tri64] using hinv0
  · simp only [show (a == 0#64) = false from by simpa using ha, Bool.false_eq_true, ite_false]
    refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
    show WP P host s _ (vals [] ++ expression [.localGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i64 .add,
      .localSet ⟨1⟩, .localGet ⟨0⟩, .intConst .i64 0xffffffffffffffff, .intBinOp .i64 .add,
      .localSet ⟨0⟩] ++ .plain (.br ⟨1⟩) :: []) _
    wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one]
    exact wp_br ⟨[], [], _, rfl, rfl, dec_lt ha, rfl, rfl, _, _, rfl, rfl, inv_dec ha hinv⟩

/-- **The Wasm problem solved** (total correctness: measure `a0`). -/
theorem spec_tactic : Spec := by
  intro a₀ _ f₀ _ P host
  rw [body_eq, locals_eq]
  simp only [Frame.forCall, List.map_cons, List.map_nil]
  show WP P host _ _ (vals [] ++ expression [.intConst .i64 0, .intConst .i64 0,
    .intBinOp .i64 .add, .localSet ⟨1⟩] ++ .plain (.loop .empty loopBody) ::
    expression [.unreachable]) _
  wasm_step [Idx.toNat, Fin.val_one]
  refine wp_loop_cons (t₁ := []) (t₂ := []) (Inv _ f₀.module a₀) ?_ (fun _ _ _ _ h => inv_body h)
    ⟨rfl, rfl, a₀, 0, rfl, rfl, by simp⟩
  rintro k s' f vs ⟨-, rfl, -, -, rfl, -⟩
  exact ⟨rfl, rfl⟩

end Spec

/-- **The RV64 problem of `sum_to` solved** (termination from the Wasm measure). -/
theorem isa_solved : ISA := isa spec_tactic

end Silmaril.Sim.RV64.Transfer.SumTo
