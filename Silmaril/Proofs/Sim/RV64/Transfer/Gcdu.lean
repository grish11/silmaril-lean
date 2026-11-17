module

public import Silmaril.Wasm.Logic.Exec.Thms
public import Silmaril.Proofs.Sim.RV64.Transfer.Generic
public import Silmaril.Sim.RV64.Cfg.Thms
public import Silmaril.WasmSpec.Rv64Gcdu.Defs
public import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `gcdu`: a loop with a call, from its Wasm problem to the RV64 problem

Cut point `0x112b8`; blocks `T0`, `T1` by `cfgSym` (`decide`). The Wasm module calls its helper
`$remu64` (the translator's M-extension helper); translation validation uses the modular call rule
of `Silmaril.Wasm.Logic.Hoare` with the spec context `Γ` holding `remuSpec` (`remu_valid`, by `wpc`).

The Wasm problem used here is `SpecInst`, the statement in the instantiated module
`Rv64Gcdu.store` (where the `call` resolves to the helper); `spec_solved` gives the generated
`Rv64Gcdu.Spec`, which has the same shape with the precondition `Pre`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Transfer.Gcdu

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym Silmaril.Sim.RV64.Cfg Silmaril.Sim.RV64.Transfer Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.VC
open Silmaril.WasmSpec.Rv64Gcdu (func program Pre Post)

def words : List (BitVec 32) :=
  [0x00058c63, 0x00058613, 0x02b575b3, 0x00060513, 0xfe059ae3, 0x00060513, 0x00008067]

def cuts : List W64 := [0x112b8#64]

def T0 : Tree2 := (Tree2.br (BranchOp.eq) (E.var 0x0b#5) (E.const 0x0000000000000000#64) (Tree2.leaf (Leaf.ret (E.var 0x0a#5))) (Tree2.leaf (Leaf.goto 0x00000000000112b8#64 [E.const 0x0000000000000000#64, E.var 0x01#5, E.var 0x02#5, E.var 0x03#5, E.var 0x04#5, E.var 0x05#5, E.var 0x06#5, E.var 0x07#5, E.var 0x08#5, E.var 0x09#5, E.var 0x0a#5, E.var 0x0b#5, E.var 0x0c#5, E.var 0x0d#5, E.var 0x0e#5, E.var 0x0f#5, E.var 0x10#5, E.var 0x11#5, E.var 0x12#5, E.var 0x13#5, E.var 0x14#5, E.var 0x15#5, E.var 0x16#5, E.var 0x17#5, E.var 0x18#5, E.var 0x19#5, E.var 0x1a#5, E.var 0x1b#5, E.var 0x1c#5, E.var 0x1d#5, E.var 0x1e#5, E.var 0x1f#5])))

def T1 : Tree2 := (Tree2.br (BranchOp.ne) (E.bin (Bin.remu) (E.var 0x0a#5) (E.var 0x0b#5)) (E.const 0x0000000000000000#64) (Tree2.leaf (Leaf.goto 0x00000000000112b8#64 [E.const 0x0000000000000000#64, E.var 0x01#5, E.var 0x02#5, E.var 0x03#5, E.var 0x04#5, E.var 0x05#5, E.var 0x06#5, E.var 0x07#5, E.var 0x08#5, E.var 0x09#5, E.bin (Bin.add) (E.bin (Bin.add) (E.var 0x0b#5) (E.const 0x0000000000000000#64)) (E.const 0x0000000000000000#64), E.bin (Bin.remu) (E.var 0x0a#5) (E.var 0x0b#5), E.bin (Bin.add) (E.var 0x0b#5) (E.const 0x0000000000000000#64), E.var 0x0d#5, E.var 0x0e#5, E.var 0x0f#5, E.var 0x10#5, E.var 0x11#5, E.var 0x12#5, E.var 0x13#5, E.var 0x14#5, E.var 0x15#5, E.var 0x16#5, E.var 0x17#5, E.var 0x18#5, E.var 0x19#5, E.var 0x1a#5, E.var 0x1b#5, E.var 0x1c#5, E.var 0x1d#5, E.var 0x1e#5, E.var 0x1f#5])) (Tree2.leaf (Leaf.ret (E.bin (Bin.add) (E.bin (Bin.add) (E.var 0x0b#5) (E.const 0x0000000000000000#64)) (E.const 0x0000000000000000#64)))))

set_option maxRecDepth 10000 in
theorem sym0 : cfgSym (codeAt 0x112b4 words) cuts 10 true 0x112b4#64 regs0 = some T0 := by decide

set_option maxRecDepth 10000 in
theorem sym1 : cfgSym (codeAt 0x112b4 words) cuts 10 true 0x112b8#64 regs0 = some T1 := by decide

/-- The helper `$remu64`. -/
def remuFunc : Func := program.funcs[1]

/-- The instantiated module. -/
def store : Store Nat := Silmaril.WasmSpec.Rv64Gcdu.store

def tyG : FnType := ⟨[.num (.int .i64), .num (.int .i64)], [.num (.int .i64)]⟩

theorem funcs : ∃ f0 f1 : FuncInst Nat, store.funcs = [f0, f1] ∧ f0.code = .wasm func ∧
    f1.code = .wasm remuFunc ∧ FnType.ofDefType? f0.type = some tyG ∧
    FnType.ofDefType? f1.type = some tyG ∧ f0.module.funcs = [0, 1] ∧ f1.module.funcs = [0, 1] := by
  have hlen : store.funcs.length = 2 := by decide +kernel
  obtain ⟨f0, f1, hf⟩ : ∃ f0 f1, store.funcs = [f0, f1] := by
    match h : store.funcs, hlen with
    | [f0, f1], _ => exact ⟨f0, f1, rfl⟩
  have hc : store.funcs.map FuncInst.code = [.wasm func, .wasm remuFunc] := rfl
  have ht : store.funcs.map (fun fi => FnType.ofDefType? fi.type) = [some tyG, some tyG] := by
    decide +kernel
  have hm : store.funcs.map (fun fi => fi.module.funcs) = [[0, 1], [0, 1]] := by decide +kernel
  rw [hf] at hc ht hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht hm
  exact ⟨f0, f1, hf, hc.1, hc.2, ht.1, ht.2, hm.1, hm.2⟩

/-! ## The helper's specification and the spec context -/

/-- `$remu64` computes `remU` (RISC-V `remu`: `x` when `y = 0`). -/
def remuSpec (f1 : FuncInst Nat) : Silmaril.Wasm.Logic.Hoare.FSpec Nat where
  pre s args := s.funcs[1]? = some f1 ∧ ∃ x y : BitVec 64, args = [.i64 x, .i64 y]
  post s args s' o := s' = s ∧ ∀ x y : BitVec 64, args = [.i64 x, .i64 y] →
    o = .normal [.i64 (remU x y)]

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
theorem remu_valid {P : Profile} {host : HostSemantics Nat} {f1 : FuncInst Nat}
    (hc : f1.code = .wasm remuFunc) (ht : FnType.ofDefType? f1.type = some tyG) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host 1 (remuSpec f1) := by
  refine FSpecValid.of_wpc_ctx (Γ := VCSpecs.empty) VCSpecs.valid_empty (fun _ _ _ _ _ _ => True)
    (fun _ _ h => h.1) hc (FnType.expand_of_ofDefType? ht) ?_ ?_
  · rintro s args ⟨-, x, y, rfl⟩; rfl
  · rintro s args ⟨-, x, y, rfl⟩
    simp [remuFunc, program, wpc, ctl, enterVC, labelQ, popI32, Silmaril.Wasm.Logic.Core.exec1,
      Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
      Frame.local?, Frame.forCall, ModuleInst.blockType?, Idx.toNat, Val.i64, Val.i32,
      intTestOp_i64, bool32, remuSpec, Silmaril.Wasm.Logic.Exec.bodyPost, remU, intBinOp]
    have h1 : (Validation.Ty.ofList (List.map ScalarType.toC tyG.results)).length = 1 := rfl
    refine ⟨fun hy => ⟨h1.symm, fun x1 y1 e1 e2 => ?_⟩, fun hy => ?_⟩
    · injection e1 with _ e1; injection e2 with _ e2
      subst e1 e2
      rw [ite_eq_left (show y = 0#64 from hy)]
    · rw [ite_eq_right hy]
      refine ⟨by rw [h1]; rfl, rfl, fun x1 y1 e1 e2 => ?_⟩
      injection e1 with _ e1; injection e2 with _ e2
      subst e1 e2
      rw [ite_eq_right (show ¬ y = 0#64 from hy)]
      rfl

/-- The spec context: `$remu64` at address `1`. -/
@[instance_reducible]
def Γr (f1 : FuncInst Nat) : VCSpecs Nat := ⟨fun a => if a = 1 then some (2, remuSpec f1) else none⟩

theorem Γr_specs1 (f1 : FuncInst Nat) : (Γr f1).specs 1 = some (2, remuSpec f1) := rfl

theorem Γr_valid {P : Profile} {host : HostSemantics Nat} {f1 : FuncInst Nat}
    (hc : f1.code = .wasm remuFunc) (ht : FnType.ofDefType? f1.type = some tyG) :
    (Γr f1).Valid P host := by
  intro a n S h
  change (if a = 1 then some (2, remuSpec f1) else none) = some (n, S) at h
  split at h
  next ha =>
    subst ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨remu_valid hc ht, fun s args hp => by simp [hp.1]⟩
  next => cases h

/-! ## Translation validation -/

/-- The simulation invariant at the Wasm loop. -/
def simInv (m₀ : MState) (s₀ : Store Nat) (mi : ModuleInst) : Invs Nat :=
  fun _ s f a => s = s₀ ∧ a = [] ∧ ∃ (σ : Reg → W64) (x : W64), Reach m₀ 0x112b8#64 σ ∧
    f = ⟨[some (.i64 (σ 10#5)), some (.i64 (σ 11#5)), some (.i64 x)], mi⟩

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
theorem tv_body (m₀ : MState) (hcode : ∀ p w, codeAt 0x112b4 words p = some w → fetch m₀.memory p = some w)
    (hpc : m₀.core.pc = 0x112b4#64) (hra : (m₀.core.read 1#5).toNat % 4 = 0)
    (f1 : FuncInst Nat) (s : Store Nat) (hs1 : s.funcs[1]? = some f1) (mi : ModuleInst)
    (hmi : mi.funcs = [0, 1]) (R : Store Nat → Silmaril.Wasm.Logic.Core.Outcome → Prop)
    (hR : ∀ v, Returns m₀ v → R s (.normal [.i64 v])) :
    wpc (Γ := Γr f1) (simInv m₀ s mi) 0 func.body (fnPost 1 R) s
      (Frame.forCall mi [.i64 (m₀.core.read 10#5), .i64 (m₀.core.read 11#5)] func.locals) [] := by
  have h0 := reach_block hcode hra sym0 (hpc ▸ reach_entry m₀)
  simp [T0, Tree2.run, BlockOut, E.eval, BranchOp.eval] at h0
  simp [func, program, wpc, ctl, enterVC, labelQ, loopQ, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
    Frame.local?, Frame.setLocal, Frame.forCall, ModuleInst.blockType?, Idx.toNat, Val.i64,
    Val.i32, simInv, defaultVal_i64, intRelOp_i64_eq, intRelOp_i64_ne, bool32, fnPost, callVC,
    callK, Γr_specs1, remuSpec, hmi, hs1]
  refine ⟨fun hz => ?_, fun hz => ⟨?_, ?_⟩⟩
  · rw [ite_eq_left hz] at h0
    simpa [Val.i64] using hR _ h0
  · rw [ite_eq_right hz] at h0
    refine ⟨_, h0, ?_, ?_, ⟨_, rfl⟩⟩ <;> simp [Leaf.vals, E.eval]
  rintro s' f' rfl σ hσ x rfl -
  have h1 := reach_block hcode hra sym1 hσ
  simp [T1, Tree2.run, BlockOut, E.eval, BranchOp.eval, Bin.eval] at h1
  simp [Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal, Val.i64, intRelOp_i64_ne, bool32,
    Γr_specs1, remuSpec, hmi, hs1, callK]
  refine ⟨⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
  rintro s1 o rfl ho
  have ho := ho _ _ rfl rfl
  subst ho
  simp [Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal, Val.i64, intRelOp_i64_ne, bool32]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [ite_eq_right hz] at h1
    refine ⟨_, h1, ?_, ?_, ⟨_, rfl⟩⟩ <;> simp [Leaf.vals, E.eval, Bin.eval]
  · rw [ite_eq_left hz] at h1
    simpa [Val.i64] using hR _ h1

/-! ## The Wasm problem in the instantiated module (total; measure `a1`) -/

section Spec

open Silmaril.Wasm.Logic.Core

variable {P : Profile} {host : HostSemantics Nat}

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- `$remu64` as a (run-existence) function specification. -/
theorem remu_funcSpec {f1 : FuncInst Nat} (hf1 : store.funcs[1]? = some f1)
    (hc : f1.code = .wasm remuFunc) (ht : FnType.ofDefType? f1.type = some tyG) :
    FuncSpec P host 1 (fun s args => s = store ∧ ∃ x y : BitVec 64, args = [.i64 x, .i64 y])
      (fun s args s' res => s' = s ∧ ∀ x y : BitVec 64, args = [.i64 x, .i64 y] →
        res = [.i64 (remU x y)]) := by
  refine FuncSpec.of_body (fun _ _ h => by rw [h.1]; exact hf1) hc (FnType.expand_of_ofDefType? ht)
    (by rintro s args ⟨-, x, y, rfl⟩; rfl) ?_
  rintro s args ⟨hs, x, y, hargs⟩
  rw [hs, hargs]
  refine wp_of_twp (fun _ _ => ⟨id, fun _ => id⟩) ?_
  have hl : loops remuFunc.body = 0 := by simp [remuFunc, program, loops, ctl]
  have h1 : (Validation.Ty.ofList (List.map ScalarType.toC tyG.results)).length = 1 := rfl
  rw [h1]
  suffices hw : wpc (fun _ _ _ _ => True) 0 remuFunc.body (funcPost P host 1 fun s' res =>
      s' = store ∧ ∀ (x1 y1 : BitVec 64), Val.i64 x = Val.i64 x1 → Val.i64 y = Val.i64 y1 →
        res = [Val.i64 (remU x1 y1)]) store
      (Frame.forCall f1.module [Val.i64 x, Val.i64 y] remuFunc.locals) [] by
    simpa [vals] using wpc_sound_total (P := P) (host := host) _ 0 remuFunc.body hl _ _ _ [] hw
  simp only [Func.body, remuFunc, program, Fin.isValue, List.getElem_cons_succ,
    List.getElem_cons_zero, Val.i64, Val.num.injEq, remU, Frame.forCall, List.map_cons,
    List.map_nil, Func.locals, List.append_nil, wpc, ctl, exec1, List.reverse_nil, localVal?,
    Frame.local?, Idx.toNat, Nat.reducePow, Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, Option.map_some,
    List.reverse_cons, List.nil_append, Val.i32, intTestOp_eqz, bool32, BitVec.ofNat_eq_ofNat,
    beq_iff_eq, popInt, popI32, ne_eq, ite_eq_right_iff, BitVec.one_eq_zero_iff,
    OfNat.ofNat_ne_zero, imp_false, not_not, enterVC, ModuleInst.blockType?, Std.le_refl,
    tsub_self, List.take_nil, funcPost, List.drop_nil, Nat.zero_mod, Nat.ofNat_pos, labelQ,
    List.cons.injEq, and_true, true_and, List.cons_append, intBinOp, Option.bind_some,
    List.length_reverse, List.reverse_eq_cons_iff]
  refine ⟨fun hy x1 y1 e1 e2 => ?_, fun hy => ?_⟩
  · have ex : x = x1 := by cases e1; rfl
    have ey : y = y1 := by cases e2; rfl
    rw [← ex, ← ey, ite_eq_left (show y = 0#64 from hy)]
  · rw [ite_eq_right hy]
    refine ⟨rfl, rfl, fun x1 y1 e1 e2 => ?_⟩
    have ex : x = x1 := by cases e1; rfl
    have ey : y = y1 := by cases e2; rfl
    rw [← ex, ← ey, ite_eq_right (show ¬ y = 0#64 from hy)]
    rfl

abbrev lg (k : Nat) : Silmaril.Wasm.Instr := .localGet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
abbrev ls (k : Nat) : Silmaril.Wasm.Instr := .localSet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
abbrev c0 : Silmaril.Wasm.Instr := .intConst .i64 0
abbrev add64 : Silmaril.Wasm.Instr := .intBinOp .i64 .add

/-- The exit branch of the loop. -/
def exitB : List Silmaril.Wasm.Instr := [lg 2, c0, add64, ls 0, .br ⟨⟨3, by decide⟩⟩]

/-- The loop body. -/
def loopB : List Silmaril.Wasm.Instr :=
  [lg 1, c0, add64, ls 2, lg 0, lg 1, .call ⟨⟨1, by decide⟩⟩, ls 1, lg 2, c0, add64, ls 0, lg 1, c0,
   .intRelOp .i64 .ne, .if_ .empty [.br ⟨⟨1, by decide⟩⟩] exitB]

set_option maxRecDepth 10000 in
theorem body_eq : func.body = [.block .empty [lg 1, c0, .intRelOp .i64 .eq,
    .if_ .empty [.br ⟨⟨1, by decide⟩⟩] [.loop .empty loopB]], lg 0, .return_, .unreachable] := rfl

theorem locals_eq : func.locals = [.num (.int .i64)] := rfl

/-- The plan's invariant (`a1 ≠ 0`, `gcd a0 a1 = gcd a0₀ a1₀`), measure `a1`. -/
def Inv (mi : ModuleInst) (a₀ a₁ : BitVec 64) : Nat → Store Nat → Frame → List Val → Prop :=
  fun k s f vs => s = store ∧ vs = [] ∧ ∃ a b c : BitVec 64,
    f = ⟨[some (.i64 a), some (.i64 b), some (.i64 c)], mi⟩ ∧ b ≠ 0 ∧ k = b.toNat ∧
    Nat.gcd a.toNat b.toNat = Nat.gcd a₀.toNat a₁.toNat

/-- The postcondition of the call. -/
abbrev Qf (a₀ a₁ : BitVec 64) : Post Nat :=
  funcPost P host 1 fun s' r => s' = store ∧ ∃ x, r = [.i64 x] ∧ Post a₀ a₁ x

/-- After the outer block: `return a0`. -/
theorem tail_ret {mi : ModuleInst} {a₀ a₁ a b c : BitVec 64}
    (h : a = BitVec.ofNat 64 (Nat.gcd a₀.toNat a₁.toNat)) :
    WP P host store ⟨[some (.i64 a), some (.i64 b), some (.i64 c)], mi⟩
      (vals [] ++ expression [lg 0, .return_, .unreachable]) (Qf (P := P) (host := host) a₀ a₁) := by
  show WP P host store _ (vals [] ++ expression [lg 0] ++ .plain .return_ :: expression [.unreachable]) _
  wasm_step [Idx.toNat]
  exact wp_return ⟨[], _, rfl, rfl, rfl, a, rfl, h⟩

theorem remU_ne {a b : BitVec 64} (hb : b ≠ 0) : remU a b = a % b := by
  simp only [remU]; exact ite_eq_right hb

theorem gcd_step (a b : BitVec 64) :
    Nat.gcd b.toNat (a % b).toNat = Nat.gcd a.toNat b.toNat := by
  rw [BitVec.toNat_umod, Nat.gcd_comm a.toNat, Nat.gcd_rec b.toNat a.toNat, Nat.gcd_comm]

theorem mod_lt' {a b : BitVec 64} (hb : b ≠ 0) : (a % b).toNat < b.toNat := by
  have : b.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using hb
  rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (by omega)

/-- The postcondition of the loop body. -/
abbrev LoopP (mi : ModuleInst) (a₀ a₁ : BitVec 64) (k : Nat) : Post Nat :=
  loopPost 0 (Inv mi a₀ a₁) k (seqPost P host [] (blockPost 0 (seqPost P host []
    (blockPost 0 (seqPost P host (expression [lg 0, .return_, .unreachable])
      (Qf (P := P) (host := host) a₀ a₁))))))

set_option maxRecDepth 10000 in
theorem inv_body {mi : ModuleInst} {a₀ a₁ : BitVec 64} (hm : mi.funcs = [0, 1])
    (hrem : FuncSpec P host 1 (fun s args => s = store ∧ ∃ x y : BitVec 64, args = [.i64 x, .i64 y])
      (fun s args s' res => s' = s ∧ ∀ x y : BitVec 64, args = [.i64 x, .i64 y] →
        res = [.i64 (remU x y)]))
    (h1 : (store.funcs[1]?).isSome) {k : Nat} {s : Store Nat} {f : Frame} {vs : List Val}
    (h : Inv mi a₀ a₁ k s f vs) :
    WP P host s f (vals vs ++ expression loopB) (LoopP (P := P) (host := host) mi a₀ a₁ k) := by
  obtain ⟨rfl, rfl, a, b, c, rfl, hb, rfl, hg⟩ := h
  show WP P host store _ (vals [] ++ expression [lg 1, c0, add64, ls 2, lg 0, lg 1] ++
    .plain (.call ⟨⟨1, by decide⟩⟩) :: expression (loopB.drop 7)) _
  wasm_step [Idx.toNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  refine wp_call (vs := []) (args := [.i64 a, .i64 b]) (by simp [hm, Idx.toNat]) h1 hrem
    ⟨rfl, a, b, rfl⟩ ?_
  rintro s' res ⟨rfl, hres⟩
  rw [hres a b rfl, remU_ne hb]
  show WP P host store _ (vals [.i64 (a % b)] ++ expression [ls 1, lg 2, c0, add64, ls 0, lg 1, c0,
    .intRelOp .i64 .ne] ++ .plain (.if_ .empty [.br ⟨⟨1, by decide⟩⟩] exitB) :: []) _
  wasm_step [Idx.toNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    Silmaril.Wasm.Logic.VC.intRelOp_i64_ne]
  refine wp_if_bool32_cons (vs := []) ?_
  by_cases hz : a % b = 0#64
  · rw [ite_eq_right (by simp [hz])]
    refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
    show WP P host store _ (vals [] ++ expression [lg 2, c0, add64, ls 0] ++
      .plain (.br ⟨⟨3, by decide⟩⟩) :: []) _
    wasm_step [Idx.toNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
    refine wp_br ?_
    simp only [blockPost, seqPost, loopPost, LoopP, Idx.toNat]
    refine ⟨[], [], rfl, rfl, tail_ret ?_⟩
    have := gcd_step a b
    rw [hz, show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.gcd_zero_right, hg] at this
    simp only [BitVec.add_zero]
    rw [← this]; simp
  · rw [ite_eq_left (by simp [hz])]
    refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
    refine wp_br ?_
    simp only [blockPost, seqPost, loopPost, LoopP, Idx.toNat]
    refine ⟨[], [], _, rfl, rfl, mod_lt' hb, rfl, rfl, b, a % b, b, by simp [Val.i64], hz, rfl, ?_⟩
    rw [gcd_step a b, hg]

set_option maxRecDepth 10000 in
/-- **The Wasm problem in the instantiated module, solved** (total; invariant and measure from
the plan). -/
theorem spec_inst (a₀ a₁ : BitVec 64) {f0 f1 : FuncInst Nat} (hm : f0.module.funcs = [0, 1])
    (hf1 : store.funcs[1]? = some f1) (hc1 : f1.code = .wasm remuFunc)
    (ht1 : FnType.ofDefType? f1.type = some tyG) :
    WP P host store (Frame.forCall f0.module [.i64 a₀, .i64 a₁] func.locals)
      (expression func.body) (Qf (P := P) (host := host) a₀ a₁) := by
  have hrem := remu_funcSpec (P := P) (host := host) hf1 hc1 ht1
  have h1 : (store.funcs[1]?).isSome := by rw [hf1]; rfl
  rw [body_eq, locals_eq]
  simp only [Frame.forCall, List.map_cons, List.map_nil, defaultVal_int64]
  show WP P host store _ (vals [] ++ .plain (.block .empty _) :: expression [lg 0, .return_, .unreachable]) _
  refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
  show WP P host store _ (vals [] ++ expression [lg 1, c0, .intRelOp .i64 .eq] ++
    .plain (.if_ .empty [.br ⟨⟨1, by decide⟩⟩] [.loop .empty loopB]) :: []) _
  wasm_step [Idx.toNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    Silmaril.Wasm.Logic.VC.intRelOp_i64_eq]
  refine wp_if_bool32_cons (vs := []) ?_
  by_cases hz : a₁ = 0#64
  · rw [ite_eq_left (by simp [hz])]
    refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
    refine wp_br ?_
    simp only [blockPost, seqPost, Idx.toNat]
    refine ⟨[], [], rfl, rfl, tail_ret ?_⟩
    subst hz
    simp
  · rw [ite_eq_right (by simp [hz])]
    refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
    show WP P host store _ (vals [] ++ .plain (.loop .empty loopB) :: []) _
    refine wp_loop_cons (t₁ := []) (t₂ := []) (Inv f0.module a₀ a₁) ?_
      (fun _ _ _ _ h => inv_body hm hrem h1 h) ⟨rfl, rfl, a₀, a₁, 0, by simp [Val.i64], hz, rfl, rfl⟩
    rintro k s f vs ⟨-, rfl, _, _, _, rfl, -⟩
    exact ⟨rfl, rfl⟩

end Spec

/-! ## The transfer -/

def PreL : List W64 → Prop := fun _ => True

def PostL : List W64 → W64 → Prop
  | [a0, a1], r => Post a0 a1 r
  | _, _ => False

/-- **The RV64 problem** of `gcdu` (contract + leaf ABI, total). -/
def ISA : Prop := FnISAP 0x112b4 words [10#5, 11#5] PreL PostL

/-- **The Wasm problem** in the instantiated module (`Rv64Gcdu.Spec` without its
precondition). -/
def SpecInst : Prop :=
  ∀ (a₀ a₁ : BitVec 64) (f0 : FuncInst Nat), store.funcs[0]? = some f0 →
    ∀ (P : Profile) (host : HostSemantics Nat),
      Silmaril.Wasm.Logic.Core.WP P host store (Frame.forCall f0.module [.i64 a₀, .i64 a₁] func.locals)
        (expression func.body) (Silmaril.Wasm.Logic.Core.funcPost P host 1 fun s' r => s' = store ∧
          ∃ x, r = [.i64 x] ∧ Post a₀ a₁ x)

theorem specInst_solved : SpecInst := by
  intro a₀ a₁ f0 hf0 P host
  obtain ⟨g0, f1, hf, -, hc1, -, ht1, hm0, -⟩ := funcs
  have : f0 = g0 := by rw [hf] at hf0; exact (Option.some.inj hf0).symm
  subst this
  exact spec_inst a₀ a₁ hm0 (by rw [hf]; rfl) hc1 ht1

/-- **The generated Wasm problem `Rv64Gcdu.Spec` solved.** -/
theorem spec_solved : Silmaril.WasmSpec.Rv64Gcdu.Spec := fun a₀ a₁ _ => specInst_solved a₀ a₁

private theorem i64_of_normal {v w : BitVec 64}
    (h : Silmaril.Wasm.Logic.Core.Outcome.normal [Val.i64 v] = .normal [Val.i64 w]) : v = w := by
  cases h; rfl

/-- **The transfer**: the Wasm problem (in the instantiated module) solves the RV64 problem. -/
theorem isa (hS : SpecInst) : ISA := by
  intro m hpc hc hra _
  obtain ⟨f0, f1, hf, hcode, hc1, ht0, ht1, hm0, -⟩ := funcs
  have hf0 : store.funcs[0]? = some f0 := by rw [hf]; rfl
  have hf1 : store.funcs[1]? = some f1 := by rw [hf]; rfl
  have he : Silmaril.Wasm.Validation.Expand f0.type tyG.toComp :=
    FnType.expand_of_ofDefType? ht0
  have hcode' : ∀ p w, codeAt 0x112b4 words p = some w → fetch m.memory p = some w :=
    code_of_codeAt hc (by decide)
  obtain ⟨s', res, hs, -, x, hres, hp⟩ := Silmaril.Wasm.Logic.Core.funcSpec_invoke_of_body
    (P := Profile.spec) (host := fun _ _ _ _ => False) (a := 0)
    (Pre := fun s args => s = store ∧ args = [.i64 (m.core.read 10#5), .i64 (m.core.read 11#5)])
    (Post := fun s _ s' res => s' = s ∧ ∃ x, res = [.i64 x] ∧
      Post (m.core.read 10#5) (m.core.read 11#5) x)
    (fun _ _ h => by rw [h.1]; exact hf0) hcode he (fun _ _ h => by rw [h.2]; rfl)
    (fun s args h => by
      obtain ⟨rfl, rfl⟩ := h
      exact hS _ _ f0 hf0 Profile.spec (fun _ _ _ _ => False)) ⟨rfl, rfl⟩
  let S : Silmaril.Wasm.Logic.Hoare.FSpec Nat :=
    { pre := fun s args => s = store ∧ args = [.i64 (m.core.read 10#5), .i64 (m.core.read 11#5)]
      post := fun _ _ _ o => ∀ v, o = .normal [.i64 v] → Returns m v }
  have hV : Silmaril.Wasm.Logic.Hoare.FSpecValid Profile.spec (fun _ _ _ _ => False) 0 S := by
    refine FSpecValid.of_wpc_fn (Γ := Γr f1) (Γr_valid hc1 ht1) (fun _ s => simInv m s f0.module)
      (fun _ _ h => by rw [h.1]; exact hf0) hcode he (fun _ _ h => by rw [h.2]; rfl) ?_
    rintro s0 args0 ⟨hs0, hargs0⟩
    rw [hs0, hargs0,
      show (Validation.Ty.ofList (List.map ScalarType.toC tyG.results)).length = 1 from rfl]
    exact tv_body m hcode' hpc hra f1 store hf1 f0.module hm0 _ fun v hv w hw =>
      i64_of_normal hw ▸ hv
  have hret : Returns m x := Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals hV
    (show S.pre store _ from ⟨rfl, rfl⟩) hs x (by rw [hres])
  obtain ⟨k, m', hrun, h1, h2, h3⟩ := hret
  exact ⟨k, m', hrun, h1, h3, by simpa [PostL, h2] using hp⟩

/-- **The RV64 problem of `gcdu` solved.** -/
theorem isa_solved : ISA := isa specInst_solved

end Silmaril.Sim.RV64.Transfer.Gcdu
