module

public import Silmaril.Wasm.Cfg.ExampleRegress.Defs
public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Games.Abstract.Module.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms
public import Silmaril.Games.Abstract.StratSession.Thms

@[expose] public section

/-!
# Regression fixtures for the self-contained CFG closure: runs (proofs)

Every activation is a run of the **logged CFG machine** (`MachineL.MStepL`), built step by step:
each block's straight-line code by `EvalLXPS` (calls open, logged with the answer the closure
then supplies), its successor by `DispL`, structured terminators by `MStepL.enter`. The machine
lemmas are generic in the store and module instance (hypotheses on the function addresses, the
global and the callee types). The closure is then resolved by `Shape.resolve_close` (`mem_close`):
internal calls by `Shape.Subst.int`, host calls by the open module's host case.

No result here goes through the native closure `Abstract.wasmEvFunXPS` or the equalities
`cfgSessionTripleC_eq`: they are proved on the CFG closure directly. The native corollaries in
`Silmaril.Wasm.Cfg.ExampleRegress.Thms` are transported along `cfgSessionTripleC_eq`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleRegress

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Cfg.CfgClosure Silmaril.Wasm.Cfg.ExampleRegress
open Silmaril.Wasm.Abstract (EvalLXPS SCall)

/-! ## Helpers -/

/-- A flat instruction, natively. -/
theorem ev_op {H : Type} {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {i : Instr}
    {es : List BExpr} {l : List (SCall H)} {r : Store H × Frame × Abstract.CallXP.POut}
    (hi : ∀ x, i ≠ .call x) (h : evalFlat s f stk i = some (s₂, f₂, .normal stk₂))
    (hk : EvalLXPS s₂ f₂ stk₂ es l r) : EvalLXPS s f stk (.op i [] :: es) l r := by
  simpa using EvalLXPS.opOk (l₁ := []) hi .nil h hk

/-- A flat instruction ending the code abruptly, natively. -/
theorem ev_stop {H : Type} {s s₂ : Store H} {f f₂ : Frame} {stk : List Val} {i : Instr}
    {es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
    (h : evalFlat s f stk i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
    EvalLXPS (H := H) s f stk (.op i [] :: es) [] (s₂, f₂, .flow fl) :=
  EvalLXPS.opStop hi .nil h hfl

/-- A behaviour of the open module, its internal calls resolved, is a behaviour of the closure. -/
theorem mem_close {sh : Abstract.Shape} {m : sh.OpenMod} {f : sh.F} {s : sh.S} {a : sh.A f}
    {x : CallBeh (sh.E ⊕ₛ sh.self) sh.S (sh.B f)} {y : CallBeh sh.E sh.S (sh.B f)}
    (hx : x ∈ m f s a) (hs : Abstract.Shape.Subst (Abstract.Shape.close m) x.1 x.2 y) :
    y ∈ Abstract.Shape.close m f s a := by
  rw [← Abstract.Shape.resolve_close]
  exact ⟨x, hx, hs⟩

/-- A stream is the concatenation of its singleton segments. -/
theorem singleton_concat {α : Type} (σ : Nat → α) : Shape.StreamConcat (fun n => [σ n]) σ := by
  have h := Shape.streamConcat_of_chain (w := fun n i => σ (i + n)) (cs := fun n => [σ n])
    (fun n => by
      funext i
      cases i with
      | zero => simp [Shape.streamAppend]
      | succ i => simp [Shape.streamAppend]; ring_nf)
    (Shape.unbounded_of_frequently _ (fun N => ⟨N, le_rfl, by simp⟩))
  simpa using h

theorem ofNat_succ (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; simp

theorem ofNat_pred (k : Nat) : BitVec.ofNat 32 (k + 1) - 1 = BitVec.ofNat 32 k := by
  rw [BitVec.ofNat_add]; simp

theorem truthy_succ {k : Nat} (hk : k + 1 < 2 ^ 32) :
    truthy (.i32 (BitVec.ofNat 32 (k + 1))) = some true := by
  have hne : BitVec.ofNat 32 (k + 1) ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  show (some (BitVec.ofNat 32 (k + 1))).map (· != 0) = some true
  simpa using hne

/-- The logged session call to the host on `n`, answered by no values in the same store. -/
abbrev hcallS {H : Type} (s : Store H) (n : BitVec 32) : SCall H :=
  SCall.mk 0 [.i32 n] s (.inl (.inl [])) s

/-- The same call, in the canonical (trap-erasing) logs. -/
abbrev hcallO (s : Store Nat) (n : Nat) : Abstract.OCall Nat :=
  Abstract.OCall.mk 0 [.i32 (BitVec.ofNat 32 n)] s (.inl []) s

/-! ## The store -/

theorem rg_f0 : ∃ fi : FuncInst Nat, rgStore.funcs[0]? = some fi ∧ fi.code = .host 0 ∧
    DefType.funcType? fi.type = some ([.i32], []) := ⟨_, rfl, rfl, rfl⟩

theorem rg_f1 : ∃ fi : FuncInst Nat, rgStore.funcs[1]? = some fi ∧
    fi.code = .wasm ⟨⟨0⟩, [], recBody⟩ ∧ DefType.funcType? fi.type = some ([.i32], []) ∧
    fi.module = rgMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem rg_f2 : ∃ fi : FuncInst Nat, rgStore.funcs[2]? = some fi ∧
    fi.code = .wasm ⟨⟨1⟩, [], trapBody⟩ ∧ DefType.funcType? fi.type = some ([], []) ∧
    fi.module = rgMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem rg_f3 : ∃ fi : FuncInst Nat, rgStore.funcs[3]? = some fi ∧
    fi.code = .wasm ⟨⟨2⟩, [], getBody⟩ ∧ DefType.funcType? fi.type = some ([], [.i32]) ∧
    fi.module = rgMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem rg_f4 : ∃ fi : FuncInst Nat, rgStore.funcs[4]? = some fi ∧
    fi.code = .wasm ⟨⟨1⟩, [.i32], pumpBody⟩ ∧ DefType.funcType? fi.type = some ([], []) ∧
    fi.module = rgMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem rgMI_funcs : rgMI.funcs = [0, 1, 2, 3, 4] := rfl

theorem rgMI_globals : rgMI.globals = [1] := rfl

theorem rg_g1 : ∃ g : GlobalInst, rgStore.globals[1]? = some g ∧ g.value = .i32 0 :=
  ⟨_, rfl, rfl⟩

theorem rg42_g1 : ∃ g : GlobalInst, rgStore42.globals[1]? = some g ∧ g.value = .i32 42 :=
  ⟨_, rfl, rfl⟩

theorem rg42_funcs : rgStore42.funcs = rgStore.funcs := rfl

/-! ## `trap` and `get` on the machine -/

section TrapGet

variable {H : Type} (s : Store H) (mi : ModuleInst) {ga : Nat} {g : GlobalInst}
  (hg : mi.globals = [ga]) (hga : s.globals[ga]? = some g)
include hg hga

/-- **`trap` on the logged machine**: one block, writing `42` to the global and trapping in the
written store. -/
theorem trap_run :
    MRunL trapBody (initial trapBody s (Frame.forCall mi [] [])) []
      ⟨.trap, [], [], s.setGlobal ga (.i32 42), Frame.forCall mi [] []⟩ := by
  have hs : evalFlat s (Frame.forCall mi [] []) [.i32 42] (.globalSet ⟨0⟩) =
      some (s.setGlobal ga (.i32 42), Frame.forCall mi [] [], .normal []) := by
    simp [evalFlat, Store.global?, Frame.forCall, hg, hga, Idx.toNat]
  have h : MStepL trapBody (initial trapBody s (Frame.forCall mi [] [])) []
      ⟨.trap, [], [], s.setGlobal ga (.i32 42), Frame.forCall mi [] []⟩ :=
    MStepL.run (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 42, .globalSet ⟨0⟩], some .unreachable⟩)
      rfl (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
      (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) hs
        (ev_stop (fun _ => nofun) rfl (by simp [Flow.IsNormal])))) DispL.trap
  simpa using MRunL.step h (.refl _)

/-- **`get` on the logged machine**: one block, exiting with the global's value. -/
theorem get_run :
    MRunL getBody (initial getBody s (Frame.forCall mi [] [])) []
      ⟨.exit, [g.value], [], s, Frame.forCall mi [] []⟩ := by
  have hs : evalFlat s (Frame.forCall mi [] []) [] (.globalGet ⟨0⟩) =
      some (s, Frame.forCall mi [] [], .normal [g.value]) := by
    simp [evalFlat, Store.global?, Frame.forCall, hg, hga, Idx.toNat]
  have h : MStepL getBody (initial getBody s (Frame.forCall mi [] [])) []
      ⟨.exit, [g.value], [], s, Frame.forCall mi [] []⟩ :=
    MStepL.run (b := ⟨[], 0⟩) (sg := ⟨[.globalGet ⟨0⟩], none⟩)
      rfl (fun _ h => nomatch h) (ev_op (fun _ => nofun) hs .nil) (DispL.next rfl)
  simpa using MRunL.step h (.refl _)

end TrapGet

/-! ## `rec` and `pump` on the machine -/

section RecPump

variable {H : Type} {s : Store H} {mi : ModuleInst} {fi0 : FuncInst H}
  (hmf : mi.funcs = [0, 1, 2, 3, 4]) (hs0 : s.funcs[0]? = some fi0)
  (ht0 : DefType.funcType? fi0.type = some ([.i32], []))
include hmf hs0 ht0

/-- **The head block of `rec n`**: `local.get 0; call 0; local.get 0` logs the host call `h(n)`,
then the `if` enters its `then` arm (`n ≠ 0`) or its empty `else` arm, which exits. -/
theorem rec_enter (n : BitVec 32) (b : Bool) (hb : truthy (.i32 n) = some b) :
    MStepL recBody (initial recBody s (Frame.forCall mi [.i32 n] [])) [hcallS s n]
      ⟨if b then .block ⟨[(0, 0)], 0⟩ else .exit, [],
        if b then [⟨0, [], false, false, [], .empty⟩] else [], s, Frame.forCall mi [.i32 n] []⟩ := by
  have hf0 : s.func? (Frame.forCall mi [.i32 n] []) ⟨0⟩ = some (0, fi0) := by
    simp [Store.func?, Frame.forCall, hmf, hs0, Idx.toNat]
  have hev : EvalLXPS s (Frame.forCall mi [.i32 n] []) []
      (liftInstrs [.localGet x0, .call ⟨0⟩, .localGet x0]) [hcallS s n]
      (s, Frame.forCall mi [.i32 n] [], .flow (.normal [.i32 n])) :=
    ev_op (fun _ => nofun) rfl (by
      exact EvalLXPS.callRet (l₁ := []) (l₂ := []) (ws := []) (s₂ := s) (stk := [.i32 n])
        (es := [.op (.localGet x0) []]) (args := []) .nil hf0 ht0 (ev_op (fun _ => nofun) rfl .nil))
  cases b
  · exact MStepL.enter (b := ⟨[], 0⟩) (a := 1) (V' := []) (np := 0) (nr := 0) rfl rfl rfl .if_ hev
      (ArmSel.cond hb) rfl rfl
  · exact MStepL.enter (b := ⟨[], 0⟩) (a := 0) (V' := []) (np := 0) (nr := 0) rfl rfl rfl .if_ hev
      (ArmSel.cond hb) rfl rfl

omit hs0 ht0 in
/-- **The `then` arm of `rec n`**: `local.get 0; i32.const 1; i32.sub; call 1` logs the recursive
internal call `rec(n - 1)`, then leaves the `if` and exits. -/
theorem rec_then {fi1 : FuncInst H} (hs1 : s.funcs[1]? = some fi1)
    (ht1 : DefType.funcType? fi1.type = some ([.i32], [])) (n : BitVec 32) :
    MStepL recBody ⟨.block ⟨[(0, 0)], 0⟩, [], [⟨0, [], false, false, [], .empty⟩], s,
        Frame.forCall mi [.i32 n] []⟩
      [SCall.mk 1 [.i32 (n - 1)] s (.inl (.inl [])) s]
      ⟨.exit, [], [], s, Frame.forCall mi [.i32 n] []⟩ := by
  have hf1 : s.func? (Frame.forCall mi [.i32 n] []) ⟨1⟩ = some (1, fi1) := by
    simp [Store.func?, Frame.forCall, hmf, hs1, Idx.toNat]
  have hev : EvalLXPS s (Frame.forCall mi [.i32 n] []) []
      (liftInstrs [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .call ⟨1⟩])
      [SCall.mk 1 [.i32 (n - 1)] s (.inl (.inl [])) s]
      (s, Frame.forCall mi [.i32 n] [], .flow (.normal [])) :=
    ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (by
      exact EvalLXPS.callRet (l₁ := []) (l₂ := []) (ws := []) (s₂ := s) (stk := [.i32 (n - 1)])
        (es := []) (args := []) .nil hf1 ht1 .nil)))
  exact MStepL.run (sg := ⟨[.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .call ⟨1⟩], none⟩)
    rfl (fun _ h => nomatch h) hev (DispL.next rfl)

/-- The `loop`'s label frame. -/
abbrev loopFr : LFrame := ⟨0, [], true, false, [], .empty⟩

/-- The machine at the body of `pump`'s loop, on the counter `k`. -/
abbrev pumpAt (s : Store H) (mi : ModuleInst) (k : BitVec 32) : MState H :=
  ⟨.block ⟨[(0, 0)], 0⟩, [], [loopFr], s, ⟨[some (.i32 k)], mi⟩⟩

omit hmf hs0 ht0 in
/-- `pump` enters its loop, the counter `0` (the local's default). -/
theorem pump_enter :
    MStepL pumpBody (initial pumpBody s (Frame.forCall mi [] [.i32])) [] (pumpAt s mi 0) :=
  MStepL.enter (b := ⟨[], 0⟩) (a := 0) (V := []) (V' := []) rfl rfl rfl .loop .nil
    (.plain (fun _ _ _ => nofun)) rfl rfl

/-- **One iteration of `pump`'s loop**: the host call `h(k)` is logged, the counter incremented,
and `br 0` re-enters the loop. -/
theorem pump_iter (k : BitVec 32) :
    MStepL pumpBody (pumpAt s mi k) [hcallS s k] (pumpAt s mi (k + 1)) := by
  have hf0 : s.func? ⟨[some (.i32 k)], mi⟩ ⟨0⟩ = some (0, fi0) := by
    simp [Store.func?, hmf, hs0, Idx.toNat]
  have hev : EvalLXPS s ⟨[some (.i32 k)], mi⟩ []
      (liftInstrs (MachineL.codeOf ⟨[.localGet x0, .call ⟨0⟩, .localGet x0, .intConst .i32 1,
        .intBinOp .i32 .add, .localSet x0], some (.br l0)⟩)) [hcallS s k]
      (s, ⟨[some (.i32 (k + 1))], mi⟩, .flow (.brk 0 [])) :=
    ev_op (fun _ => nofun) rfl (by
      exact EvalLXPS.callRet (l₁ := []) (l₂ := []) (ws := []) (s₂ := s) (stk := [.i32 k])
        (args := []) .nil hf0 ht0
        (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl
          (ev_op (fun _ => nofun) rfl (ev_stop (fun _ => nofun) rfl (by simp [Flow.IsNormal])))))))
  exact MStepL.run rfl (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk) hev
    (DispL.br (k := 0) (L := loopFr) rfl rfl)

end RecPump

/-! ## The fixtures on the CFG closure -/

section Closure

variable {s : Store Nat} (hf : s.funcs = rgStore.funcs)
include hf

/-- **The host function in the CFG session closure**: one host call. -/
theorem host_beh (n : BitVec 32) :
    ([hostAt s n], End.ret (.inl (.inl [])) s) ∈ Shape.close cfgHOpenXPS 0 s [.i32 n] := by
  obtain ⟨fi, hfi, hc, hty⟩ := rg_f0
  exact mem_close
    (x := (([⟨.inl (0, s, [.i32 n]), (s, Result.values [])⟩] : List (SCall Nat)), _))
    (.inr (.inr ⟨fi, 0, [.i32], [], s, .values [], .normal [], hf ▸ hfi, hc, hty, rfl, rfl⟩))
    (.ext (.nil _))

/-- **The host function in the canonical CFG closure.** -/
theorem host_behX (n : BitVec 32) :
    ([hostAt s n], End.ret (.inl []) s) ∈ Shape.close cfgHOpenXP 0 s [.i32 n] := by
  obtain ⟨fi, hfi, hc, hty⟩ := rg_f0
  exact mem_close
    (x := (([⟨.inl (0, s, [.i32 n]), (s, Result.values [])⟩] : List (Abstract.HCall Nat)), _))
    (.inr (.inr ⟨fi, 0, [.i32], [], s, .values [], .normal [], hf ▸ hfi, hc, hty, rfl, rfl⟩))
    (.ext (.nil _))

/-- **The open log of `rec (k + 1)` on the machine**: the host call `h(k + 1)`, then the
recursive internal call `rec k`, then the exit. -/
theorem rec_run (k : Nat) (hk : k + 1 < 2 ^ 32) :
    MRunL recBody (initial recBody s (Frame.forCall rgMI [.i32 (BitVec.ofNat 32 (k + 1))] []))
      [hcallS s (BitVec.ofNat 32 (k + 1)),
        SCall.mk 1 [.i32 (BitVec.ofNat 32 k)] s (.inl (.inl [])) s]
      ⟨.exit, [], [], s, Frame.forCall rgMI [.i32 (BitVec.ofNat 32 (k + 1))] []⟩ := by
  obtain ⟨fi0, hfi0, -, hty0⟩ := rg_f0
  obtain ⟨fi1, hfi1, -, hty1, -⟩ := rg_f1
  rw [← hf] at hfi0 hfi1
  have hr := MRunL.step (rec_enter rgMI_funcs hfi0 hty0 _ true (truthy_succ hk))
    (MRunL.step (rec_then rgMI_funcs hfi1 hty1 _) (.refl _))
  rw [ofNat_pred] at hr
  simpa using hr

/-- **`rec k` in the CFG session closure**: the host calls `recLog s k`, one per depth. -/
theorem rec_beh (k : Nat) (hk : k < 2 ^ 32) :
    (recLog s k, End.ret (.inl (.inl [])) s) ∈
      Shape.close cfgHOpenXPS 1 s [.i32 (BitVec.ofNat 32 k)] := by
  obtain ⟨fi0, hfi0, -, hty0⟩ := rg_f0
  obtain ⟨fi1, hfi1, hc1, hty1, hm1⟩ := rg_f1
  rw [← hf] at hfi0 hfi1
  induction k with
  | zero =>
    have hr := MRunL.step (rec_enter rgMI_funcs hfi0 hty0 0 false rfl) (.refl _)
    refine mem_close (x := ([hcallS s 0], _)) (.inl ⟨fi1, _, [.i32], [],
      ⟨.exit, [], [], s, Frame.forCall rgMI [.i32 0] []⟩, .normal [], .normal [], _,
      hfi1, hc1, hty1, by rw [hm1]; simpa using hr, trivial, ⟨_, rfl, rfl⟩, rfl, rfl⟩) ?_
    exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS) (g := 0)
      (host_beh hf 0) (.nil _)
  | succ k ih =>
    have ih := ih (by omega)
    refine mem_close
      (x := ([hcallS s _, SCall.mk 1 [.i32 (BitVec.ofNat 32 k)] s (.inl (.inl [])) s], _))
      (.inl ⟨fi1, _, [.i32], [],
        ⟨.exit, [], [], s, Frame.forCall rgMI [.i32 (BitVec.ofNat 32 (k + 1))] []⟩,
        .normal [], .normal [], _, hfi1, hc1, hty1, by rw [hm1]; exact rec_run hf k hk, trivial, ⟨_, rfl, rfl⟩, rfl,
        rfl⟩) ?_
    have h := Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
      (host_beh hf (BitVec.ofNat 32 (k + 1))) (Shape.Subst.int (sh := Abstract.wasmHShapeS Nat)
        (c := Shape.close cfgHOpenXPS) ih (.nil (Abstract.endOfFlowS (Flow.normal []) s)))
    simp only [List.append_nil, List.singleton_append] at h
    exact h

/-- **`get` in the CFG session closure** answers the global's value, keeping the store. -/
theorem get_beh {g : GlobalInst} (hg : s.globals[1]? = some g) :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inl (.inl [g.value])) s) ∈
      Shape.close cfgHOpenXPS 3 s [] := by
  obtain ⟨fi, hfi, hc, hty, hm⟩ := rg_f3
  exact mem_close (x := ([], _)) (.inl ⟨fi, _, [], [.i32],
    ⟨.exit, [g.value], [], s, Frame.forCall rgMI [] []⟩, .normal [g.value],
    .normal [g.value], [], hf ▸ hfi, hc, hty, by rw [hm]; exact get_run s rgMI rgMI_globals hg,
    trivial,
    ⟨_, rfl, rfl⟩, rfl, rfl⟩) (.nil _)

/-- **`pump` runs productively on the logged machine**, its stream the host calls `h(0), h(1), …`
(the counter read modulo `2 ^ 32`). -/
theorem pump_prod :
    ProdL pumpBody (initial pumpBody s (Frame.forCall rgMI [] [.i32]))
      (fun n => (hcallO s n).toS) := by
  obtain ⟨fi0, hfi0, -, hty0⟩ := rg_f0
  rw [← hf] at hfi0
  refine ⟨fun n => Nat.casesOn n (initial pumpBody s (Frame.forCall rgMI [] [.i32]))
      (fun n => pumpAt s rgMI (BitVec.ofNat 32 n)),
    [[]] ++ω (fun n => [hcallS s (BitVec.ofNat 32 n)]), rfl, fun n => ?_, ?_⟩
  · cases n with
    | zero => exact pump_enter
    | succ n =>
      have h := pump_iter rgMI_funcs hfi0 hty0 (BitVec.ofNat 32 n)
      rw [ofNat_succ] at h
      simpa [Shape.streamAppend] using h
  · have h := Shape.streamConcat_append (ls := [[]])
      (singleton_concat (fun n => hcallS s (BitVec.ofNat 32 n)))
    simpa [Shape.streamAppend_nil] using h

/-- **`pump`'s productive stream in the CFG closure**: the host calls `h(0), h(1), …`. -/
theorem pump_inf : (fun n => hostAt s (BitVec.ofNat 32 n)) ∈ cfgEvInfNXP s (4, []) := by
  obtain ⟨fi4, hfi4, hc4, -, hm4⟩ := rg_f4
  rw [← hf] at hfi4
  refine .inr ⟨⟨4, ([], s)⟩, [], fun i => (hcallO s i).lift, fun n => hostAt s (BitVec.ofNat 32 n),
    .refl _, ⟨fi4, _, fun n => hcallO s n, hfi4, hc4, by rw [hm4]; exact pump_prod hf, rfl⟩,
    ⟨fun i => [hostAt s (BitVec.ofNat 32 i)], fun i => .int (host_behX hf _), singleton_concat _⟩,
    (Shape.streamAppend_nil _).symm⟩

end Closure

/-- **`trap` in the CFG session closure**: it traps, keeping the store it wrote. -/
theorem trap_beh :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inr ()) rgStore42) ∈
      Shape.close cfgHOpenXPS 2 rgStore [] := by
  obtain ⟨fi, hfi, hc, hty, hm⟩ := rg_f2
  obtain ⟨g, hg, -⟩ := rg_g1
  exact mem_close (x := ([], _)) (.inl ⟨fi, _, [], [],
    ⟨.trap, [], [], rgStore42, Frame.forCall rgMI [] []⟩, .trap, .trap, [], hfi, hc, hty,
    by rw [hm]; exact trap_run rgStore rgMI rgMI_globals hg, trivial, rfl, rfl, rfl⟩) (.nil _)

/-! ## The fixtures in the CFG session triple and its sessions -/

section Session

open StratSession
open StratThread (streamPlay Rounds)

/-- The session triple at the fixtures' host type. -/
abbrev tC : ObsTriple (Abstract.wasmHostSig Nat) (Store Nat) (Nat × List Val)
    ((List Val ⊕ Nat) ⊕ PUnit.{1}) := cfgSessionTripleC

theorem rec_log (k : Nat) (hk : k < 2 ^ 32) :
    (recLog rgStore k, End.ret (.inl (.inl [])) rgStore) ∈
      cfgEvFunDXPSC rgStore (1, [.i32 (BitVec.ofNat 32 k)]) :=
  .inl (rec_beh rfl k hk)

theorem rec_session (k : Nat) (hk : k < 2 ^ 32) :
    sroundsMoves [((1, [.i32 (BitVec.ofNat 32 k)]), recLog rgStore k, .inl (.inl []))] ∈
      (threadS tC rgStore).toStrategy :=
  mem_srounds_snoc_ret (rs := []).2 ⟨rgStore, .cons (rec_log k hk) (.nil _)⟩

theorem trap_round :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inr ()) rgStore42) ∈
      cfgEvFunDXPSC rgStore (2, []) :=
  .inl trap_beh

theorem get_round :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inl (.inl [.i32 42])) rgStore42) ∈
      cfgEvFunDXPSC rgStore42 (3, []) := by
  obtain ⟨g, hg, hv⟩ := rg42_g1
  have h := get_beh rg42_funcs hg
  rw [hv] at h
  exact .inl h

theorem get_fresh :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inl (.inl [.i32 0])) rgStore) ∈
      cfgEvFunDXPSC rgStore (3, []) := by
  obtain ⟨g, hg, hv⟩ := rg_g1
  have h := get_beh rfl hg
  rw [hv] at h
  exact .inl h

theorem trap_then_get :
    ([.inr (.ask (2, [])), .inr (.ans (2, []) (.inr PUnit.unit)), .inr (.ask (3, [])),
        .inr (.ans (3, []) (.inl (.inl [.i32 42])))] :
        List (Move (Abstract.wasmHostSig Nat) (sig1 (Nat × List Val) (List Val ⊕ Nat)))) ∈
      (threadS tC rgStore).toStrategy :=
  mem_trap_ret_nil.2 ⟨rgStore42, trap_round, rgStore42, get_round⟩

theorem pump_session :
    streamPlay [] (4, []) (fun n => hostAt rgStore (BitVec.ofNat 32 n)) ∈ (threadS tC rgStore).inf :=
  StratSession.mem_inf (rs := []).2 ⟨rgStore, .nil _, pump_inf rfl⟩

theorem regress_play :
    streamPlay (sroundsMoves [((2, []), [], .inr PUnit.unit), ((3, []), [], .inl (.inl [.i32 42]))])
      (4, []) (fun n => hostAt rgStore42 (BitVec.ofNat 32 n)) ∈ (threadS tC rgStore).inf :=
  StratSession.mem_inf.2 ⟨rgStore42, .cons trap_round (.cons get_round (.nil _)), pump_inf rg42_funcs⟩

end Session

end Silmaril.Wasm.Cfg.Proofs.ExampleRegress
