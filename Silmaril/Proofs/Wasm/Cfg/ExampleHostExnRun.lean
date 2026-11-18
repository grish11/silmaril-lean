module

public import Silmaril.Wasm.Cfg.ExampleHostExn.Defs
public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Games.Abstract.Module.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Proofs.Wasm.Cfg.ExampleRegressRun

@[expose] public section

/-!
# Host exceptions and traps under `try_table`, on the CFG closure: runs (proofs)

Every activation is an explicit run of the **logged CFG machine** (`MachineL.MStepL`): the entry
block enters the `try_table` arm (`MStepL.enter`, pushing the handler's label frame `tryFr` or
`tryAllFr`), then the arm's block runs its straight-line code by `EvalLXPS`, the call to the host
logged open with its answer (`callThrow`, `callTrap`), and moves on by `DispL` (`catchOut`: the
exception caught by the handler frame, to the function label; `trap`), or ends in a pending tail
call (`TailL`, the `return_call` made when the function's frame is left). The closure is resolved
by `Shape.resolve_close` (`Proofs.ExampleRegress.mem_close`), the host call by the open module's
host case. Nothing here goes through the native closure.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleHostExn

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Cfg.CfgClosure Silmaril.Wasm.Cfg.ExampleHostExn
open Silmaril.Wasm.Abstract (EvalLXPS SCall ReachLXPS endOfFlowS exitFlow resFlow)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.ExampleRegress (mem_close)

/-! ## The store -/

theorem hx_f0 : ∃ fi : FuncInst Nat, hxStore.funcs[0]? = some fi ∧ fi.code = .host 0 ∧
    DefType.funcType? fi.type = some ([], [.i32]) := ⟨_, rfl, rfl, rfl⟩

theorem hx_f1 : ∃ fi : FuncInst Nat, hxStore.funcs[1]? = some fi ∧
    fi.code = .wasm ⟨⟨1⟩, [], callBody⟩ ∧ DefType.funcType? fi.type = some ([], [.i32]) ∧
    fi.module = hxMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem hx_f2 : ∃ fi : FuncInst Nat, hxStore.funcs[2]? = some fi ∧
    fi.code = .wasm ⟨⟨1⟩, [], tailBody⟩ ∧ DefType.funcType? fi.type = some ([], [.i32]) ∧
    fi.module = hxMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem hx_f3 : ∃ fi : FuncInst Nat, hxStore.funcs[3]? = some fi ∧
    fi.code = .wasm ⟨⟨2⟩, [], trapBody⟩ ∧ DefType.funcType? fi.type = some ([], []) ∧
    fi.module = hxMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem hxMI_funcs : hxMI.funcs = [0, 1, 2, 3] := rfl

theorem hxMI_tags : hxMI.tags = [0] := rfl

theorem hxStore_exns : hxStore.exns = [] := rfl

theorem hxThrown_funcs (v : BitVec 32) : (hxThrown v).funcs = hxStore.funcs := rfl

/-! ## The machine -/

/-- The label frame of the `try_table (result i32) (catch 0 0)` of `callH` and `tailH`. -/
abbrev tryFr : LFrame := ⟨1, [], false, true, [catchE], .value .i32⟩

/-- The label frame of the `try_table (catch_all 0)` of `trapH`. -/
abbrev tryAllFr : LFrame := ⟨0, [], false, true, [.catchAll l0], .empty⟩

/-- The machine inside the `try_table` arm (block `[(0, 0)]`, index `0`), under the frame `L`. -/
abbrev armAt {H : Type} (L : LFrame) (s : Store H) (f : Frame) : MState H :=
  ⟨.block ⟨[(0, 0)], 0⟩, [], [L], s, f⟩

section Machine

variable {H : Type} {s s' : Store H} {f : Frame} {fi0 : FuncInst H}

/-- `callH` enters its `try_table`, pushing the handler frame. -/
theorem call_enter : MStepL callBody (initial callBody s f) [] (armAt tryFr s f) :=
  MStepL.enter (b := ⟨[], 0⟩) (a := 0) (V := []) (V' := []) rfl rfl rfl .tryTable .nil
    (.plain (fun _ _ _ => nofun)) rfl rfl

/-- `tailH` enters its `try_table`, pushing the handler frame. -/
theorem tail_enter : MStepL tailBody (initial tailBody s f) [] (armAt tryFr s f) :=
  MStepL.enter (b := ⟨[], 0⟩) (a := 0) (V := []) (V' := []) rfl rfl rfl .tryTable .nil
    (.plain (fun _ _ _ => nofun)) rfl rfl

/-- `trapH` enters its `try_table`, pushing the handler frame. -/
theorem trap_enter : MStepL trapBody (initial trapBody s f) [] (armAt tryAllFr s f) :=
  MStepL.enter (b := ⟨[], 0⟩) (a := 0) (V := []) (V' := []) rfl rfl rfl .tryTable .nil
    (.plain (fun _ _ _ => nofun)) rfl rfl

variable (hf0 : s.func? f ⟨0⟩ = some (0, fi0))

include hf0 in
/-- **The host call of `callH` is pending inside the handler**: the arm's block reaches the call
`h()`, the handler frame `tryFr` on the label stack. -/
theorem call_reach (ht0 : DefType.funcType? fi0.type = some ([], [.i32])) :
    ReachL callBody (armAt tryFr s f) [] ⟨0, ([], s)⟩ :=
  ReachL.run rfl (fun _ h => nomatch h) (ReachLXPS.call (es := []) (stk := []) .nil hf0 ht0)

include hf0 in
/-- **The host call of `callH` answered by an exception the handler catches**: `catch 0 0`
branches to the function label with the exception's fields. -/
theorem call_catch (ht0 : DefType.funcType? fi0.type = some ([], [.i32])) {t : Nat} {e : ExnInst}
    (he : s'.exns[t]? = some e) (htag : f.module.tags[0]? = some e.tag) :
    MStepL callBody (armAt tryFr s f) [SCall.mk 0 [] s (.inl (.inr t)) s']
      ⟨.exit, e.fields, [], s', f⟩ := by
  have h := MStepL.run (body := callBody) (b := ⟨[(0, 0)], 0⟩) (ls := [tryFr]) (stk := []) rfl
    (fun _ h => nomatch h)
    (EvalLXPS.callThrow (es := []) (stk := []) (t := t) (s₂ := s') .nil hf0 ht0)
    (DispL.catchOut (j := 0) (l := l0) (fun _ _ hk => absurd hk (Nat.not_lt_zero _)) rfl rfl
      (Catches.catch_ he htag) rfl)
  simpa using h

include hf0 in
/-- **A host exception under `catch_all`** is caught: a branch to the function label, no
values. -/
theorem trap_catch (ht0 : DefType.funcType? fi0.type = some ([], [.i32])) (t : Nat) :
    MStepL trapBody (armAt tryAllFr s f) [SCall.mk 0 [] s (.inl (.inr t)) s']
      ⟨.exit, [], [], s', f⟩ := by
  have h := MStepL.run (body := trapBody) (b := ⟨[(0, 0)], 0⟩) (ls := [tryAllFr]) (stk := []) rfl
    (fun _ h => nomatch h)
    (EvalLXPS.callThrow (es := [.op .drop []]) (stk := []) (t := t) (s₂ := s') .nil hf0 ht0)
    (DispL.catchOut (j := 0) (l := l0) (fun _ _ hk => absurd hk (Nat.not_lt_zero _)) rfl rfl
      Catches.catchAll rfl)
  simpa using h

include hf0 in
/-- **A host trap under `catch_all`** is not caught: the machine moves to `trap`, in the host's
store. -/
theorem trap_trap (ht0 : DefType.funcType? fi0.type = some ([], [.i32])) :
    MStepL trapBody (armAt tryAllFr s f) [SCall.mk 0 [] s (.inr ()) s']
      ⟨.trap, [], [], s', f⟩ := by
  have h := MStepL.run (body := trapBody) (b := ⟨[(0, 0)], 0⟩) (ls := [tryAllFr]) (stk := []) rfl
    (fun _ h => nomatch h)
    (EvalLXPS.callTrap (es := [.op .drop []]) (stk := []) (s₂ := s') .nil hf0 ht0) DispL.trap
  simpa using h

include hf0 in
/-- **The `return_call` of `tailH` ends the body** in a pending tail call to `h` (result arity
`1`), through the handler frame: it is made when the function's frame is left. -/
theorem tail_tail (hfa : s.funcs[0]? = some fi0)
    (ht0 : DefType.funcType? fi0.type = some ([], [.i32])) :
    TailL tailBody (armAt tryFr s f) [] (s, f, .tail 0 [] 1) :=
  TailL.tail rfl (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
    (EvalLXPS.tail (es := []) (stk := []) (ps := []) (rs := [.i32]) .nil (.direct hf0) hfa ht0
      (fun _ h => by simp [Abstract.CallXT.tailAnn] at h))

end Machine

/-! ## The functions on the CFG closure -/

section Closure

variable {s : Store Nat} (hf : s.funcs = hxStore.funcs)
include hf

/-- The frame of a call to `callH`, `tailH` or `trapH` (no arguments, no locals). -/
abbrev fr0 : Frame := Frame.forCall hxMI [] []

theorem f0_of : ∃ fi0 : FuncInst Nat, s.funcs[0]? = some fi0 ∧ s.func? fr0 ⟨0⟩ = some (0, fi0) ∧
    fi0.code = .host 0 ∧ DefType.funcType? fi0.type = some ([], [.i32]) := by
  obtain ⟨fi0, hfi0, hc, hty⟩ := hx_f0
  rw [← hf] at hfi0
  exact ⟨fi0, hfi0, by simp [Store.func?, Frame.forCall, hxMI_funcs, hfi0, Idx.toNat], hc, hty⟩

/-- **The host function in the CFG session closure**: one host call `h()`, answered by `r`
leaving `s'`, ending as `r` read at the result arity `1`. -/
theorem host_beh (r : Result) (fl : Flow) (hfl : exitFlow 1 (resFlow r) = some fl)
    (s' : Store Nat) :
    ([hostAns s r s'], endOfFlowS fl s') ∈ Shape.close cfgHOpenXPS 0 s [] := by
  obtain ⟨fi, hfi, -, hc, hty⟩ := f0_of hf
  exact mem_close (x := (([⟨.inl (0, s, []), (s', r)⟩] : List (SCall Nat)), _))
    (.inr (.inr ⟨fi, 0, [], [.i32], s', r, fl, hfi, hc, hty, hfl, rfl⟩)) (.ext (.nil _))

/-- **`callH` with the host throwing an exception of `$e`**: caught by `catch 0 0`; `callH`
returns the payload `w`, in the host's store. -/
theorem callH_caught {s' : Store Nat} {t : Nat} {w : Val} (he : s'.exns[t]? = some ⟨0, [w]⟩) :
    ([hostAns s (.throw t) s'], End.ret (.inl (.inl [w])) s') ∈
      Shape.close cfgHOpenXPS 1 s [] := by
  obtain ⟨fi0, -, hf0, -, ht0⟩ := f0_of hf
  obtain ⟨fi1, hfi1, hc1, hty1, hm1⟩ := hx_f1
  rw [← hf] at hfi1
  have hr : MRunL callBody (initial callBody s fr0) [SCall.mk 0 [] s (.inl (.inr t)) s']
      ⟨.exit, [w], [], s', fr0⟩ :=
    MRunL.step call_enter (MRunL.step (call_catch hf0 ht0 he rfl) (.refl _))
  refine mem_close (x := ([SCall.mk 0 [] s (.inl (.inr t)) s'], _)) (.inl ⟨fi1, _, [], [.i32],
    ⟨.exit, [w], [], s', fr0⟩, .normal [w], .normal [w], _, hfi1, hc1, hty1,
    by rw [hm1]; exact hr, trivial, ⟨_, rfl, rfl⟩, rfl, rfl⟩) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    (host_beh hf (.throw t) (.throw t) rfl s') (.nil _)

/-- **`tailH` with the host throwing**: the `return_call` is made when `tailH`'s frame is left,
outside its handler; the exception is not caught, whatever store and exception the host
answers with. -/
theorem tailH_uncaught (t : Nat) (s' : Store Nat) :
    ([hostAns s (.throw t) s'], End.ret (.inl (.inr t)) s') ∈ Shape.close cfgHOpenXPS 2 s [] := by
  obtain ⟨fi0, hfa, hf0, -, ht0⟩ := f0_of hf
  obtain ⟨fi2, hfi2, hc2, hty2, hm2⟩ := hx_f2
  rw [← hf] at hfi2
  refine mem_close (x := ([SCall.mk 0 [] s (.inl (.inr t)) s'], _)) (.inr (.inl ⟨fi2, _, [],
    [.i32], armAt tryFr s fr0, s, s', fr0, 0, 1, [], .inl (.inr t), [], [], hfi2, hc2, hty2,
    by rw [hm2]; exact MRunL.step tail_enter (.refl _), tail_tail hf0 hfa ht0, rfl⟩)) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    (host_beh hf (.throw t) (.throw t) rfl s') (.nil _)

/-- **`trapH` with the host trapping**: `catch_all` does not catch a trap; `trapH` traps in the
host's store. -/
theorem trapH_trap (s' : Store Nat) :
    ([hostAns s .trap s'], End.ret (.inr ()) s') ∈ Shape.close cfgHOpenXPS 3 s [] := by
  obtain ⟨fi0, -, hf0, -, ht0⟩ := f0_of hf
  obtain ⟨fi3, hfi3, hc3, hty3, hm3⟩ := hx_f3
  rw [← hf] at hfi3
  refine mem_close (x := ([SCall.mk 0 [] s (.inr ()) s'], _)) (.inl ⟨fi3, _, [], [],
    ⟨.trap, [], [], s', fr0⟩, .trap, .trap, _, hfi3, hc3, hty3,
    by rw [hm3]; exact MRunL.step trap_enter (MRunL.step (trap_trap hf0 ht0) (.refl _)), trivial,
    rfl, rfl, rfl⟩) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    (host_beh hf .trap .trap rfl s') (.nil _)

/-- **`trapH` with the host throwing**: `catch_all` catches any exception; `trapH` returns no
values, in the host's store. -/
theorem trapH_caught (t : Nat) (s' : Store Nat) :
    ([hostAns s (.throw t) s'], End.ret (.inl (.inl [])) s') ∈ Shape.close cfgHOpenXPS 3 s [] := by
  obtain ⟨fi0, -, hf0, -, ht0⟩ := f0_of hf
  obtain ⟨fi3, hfi3, hc3, hty3, hm3⟩ := hx_f3
  rw [← hf] at hfi3
  refine mem_close (x := ([SCall.mk 0 [] s (.inl (.inr t)) s'], _)) (.inl ⟨fi3, _, [], [],
    ⟨.exit, [], [], s', fr0⟩, .normal [], .normal [], _, hfi3, hc3, hty3,
    by rw [hm3]; exact MRunL.step trap_enter (MRunL.step (trap_catch hf0 ht0 t) (.refl _)),
    trivial, ⟨_, rfl, rfl⟩, rfl, rfl⟩) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    (host_beh hf (.throw t) (.throw t) rfl s') (.nil _)

/-- **`callH`'s pending host call**: no log before it, made inside the handler (`ReachL` from the
machine state with the handler frame). -/
theorem callH_pend : (([] : List (Call (Abstract.wasmHostSig Nat))), ((0 : Nat), s, ([] : List Val)))
    ∈ cfgEvPendXPS s (1, []) := by
  obtain ⟨fi0, hfa, hf0, hc0, ht0⟩ := f0_of hf
  obtain ⟨fi1, hfi1, hc1, -, hm1⟩ := hx_f1
  rw [← hf] at hfi1
  have h := CfgPendLXPS.desc (q := []) hfi1 hc1 (by rw [hm1]; exact MRunL.step call_enter (.refl _))
    (call_reach hf0 ht0) .nil (CfgPendLXPS.self (vs := []) hfa hc0)
  exact h

/-- **`tailH`'s pending host call**: no log before it, made as the pending tail call (`TailL`)
when the frame is left. -/
theorem tailH_pend : (([] : List (Call (Abstract.wasmHostSig Nat))), ((0 : Nat), s, ([] : List Val)))
    ∈ cfgEvPendXPS s (2, []) := by
  obtain ⟨fi0, hfa, hf0, hc0, ht0⟩ := f0_of hf
  obtain ⟨fi2, hfi2, hc2, -, hm2⟩ := hx_f2
  rw [← hf] at hfi2
  have h := CfgPendLXPS.tail (q := []) hfi2 hc2 (by rw [hm2]; exact MRunL.step tail_enter (.refl _))
    (tail_tail hf0 hfa ht0) .nil (CfgPendLXPS.self (vs := []) hfa hc0)
  exact h

end Closure

/-! ## The machine at the pending calls, from `hxStore` -/

theorem callH_pend_machine :
    MRunL callBody (initial callBody hxStore fr0) [] (armAt tryFr hxStore fr0) ∧
      ReachL callBody (armAt tryFr hxStore fr0) [] ⟨0, ([], hxStore)⟩ := by
  obtain ⟨fi0, -, hf0, -, ht0⟩ := f0_of (s := hxStore) rfl
  exact ⟨MRunL.step call_enter (.refl _), call_reach hf0 ht0⟩

theorem tailH_pend_machine :
    MRunL tailBody (initial tailBody hxStore fr0) [] (armAt tryFr hxStore fr0) ∧
      TailL tailBody (armAt tryFr hxStore fr0) [] (hxStore, fr0, .tail 0 [] 1) := by
  obtain ⟨fi0, hfa, hf0, -, ht0⟩ := f0_of (s := hxStore) rfl
  exact ⟨MRunL.step tail_enter (.refl _), tail_tail hf0 hfa ht0⟩

/-! ## The fixtures in the CFG session triple and its sessions -/

section Session

open StratSession
open StratThread (Rounds)

/-- The session triple at the fixtures' host type. -/
abbrev tC : ObsTriple (Abstract.wasmHostSig Nat) (Store Nat) (Nat × List Val)
    ((List Val ⊕ Nat) ⊕ PUnit.{1}) := cfgSessionTripleC

theorem callH_round (v : BitVec 32) :
    ([hostAns hxStore (.throw 0) (hxThrown v)], End.ret (.inl (.inl [.i32 v])) (hxThrown v)) ∈
      cfgEvFunDXPSC hxStore (1, []) :=
  .inl (callH_caught rfl rfl)

theorem callH_round_existing (v : BitVec 32) :
    ([hostAns (hxThrown v) (.throw 0) (hxThrown v)], End.ret (.inl (.inl [.i32 v])) (hxThrown v)) ∈
      cfgEvFunDXPSC (hxThrown v) (1, []) :=
  .inl (callH_caught (hxThrown_funcs v) rfl)

theorem tailH_round (v : BitVec 32) :
    ([hostAns hxStore (.throw 0) (hxThrown v)], End.ret (.inl (.inr 0)) (hxThrown v)) ∈
      cfgEvFunDXPSC hxStore (2, []) :=
  .inl (tailH_uncaught rfl 0 _)

theorem tailH_round_existing (v : BitVec 32) :
    ([hostAns (hxThrown v) (.throw 0) (hxThrown v)], End.ret (.inl (.inr 0)) (hxThrown v)) ∈
      cfgEvFunDXPSC (hxThrown v) (2, []) :=
  .inl (tailH_uncaught (hxThrown_funcs v) 0 _)

theorem trapH_round (s' : Store Nat) :
    ([hostAns hxStore .trap s'], End.ret (.inr ()) s') ∈ cfgEvFunDXPSC hxStore (3, []) :=
  .inl (trapH_trap rfl s')

theorem trapH_round_throw (t : Nat) (s' : Store Nat) :
    ([hostAns hxStore (.throw t) s'], End.ret (.inl (.inl [])) s') ∈
      cfgEvFunDXPSC hxStore (3, []) :=
  .inl (trapH_caught rfl t s')

theorem exn_session :
    sroundsMoves [((1, []), [hostAns hxStore (.throw 0) (hxThrown 42)], .inl (.inl [.i32 42])),
        ((2, []), [hostAns (hxThrown 42) (.throw 0) (hxThrown 42)], .inl (.inr 0))] ∈
      (threadS tC hxStore).toStrategy :=
  mem_srounds_snoc_ret (rs := [_]).2
    ⟨_, .cons (callH_round 42) (.cons (tailH_round_existing 42) (.nil _))⟩

theorem pend_session :
    sroundsMoves [((1, []), [hostAns hxStore (.throw 0) (hxThrown 42)], .inl (.inl [.i32 42]))] ++
        .inr (.ask (2, [])) :: [.inl (.ask ((0 : Nat), hxThrown 42, []))] ∈
      (threadS tC hxStore).toStrategy :=
  mem_pending (c := []).2 ⟨hxThrown 42, .cons (callH_round 42) (.nil _), .inl (tailH_pend (hxThrown_funcs 42))⟩

theorem trap_session :
    sroundMoves ((3, []), [hostAns hxStore .trap (hxThrown 42)], .inr PUnit.unit) ++
        sroundMoves ((1, []), [hostAns (hxThrown 42) (.throw 0) (hxThrown 42)],
          .inl (.inl [.i32 42])) ∈
      (threadS tC hxStore).toStrategy :=
  mem_trap_ret.2 ⟨hxThrown 42, trapH_round _, hxThrown 42, callH_round_existing 42⟩

end Session

end Silmaril.Wasm.Cfg.Proofs.ExampleHostExn
