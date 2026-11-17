module

public import Silmaril.Wasm.Cfg.MachineL.Defs

/-!
# The recursive CFG closure: definitions (H3)

`cfgHOpenXPS`: the open module whose Wasm functions run **on the logged block-CFG machine**
(`MachineL.MStepL`), as the session's open module `Abstract.wasmHOpenXPS` runs them by the native
relation `EvalLXPS`. It is defined from the machine, not as an alias:

* a Wasm function whose body runs from the CFG entry (`initial`, the call's frame
  `Frame.forCall`) to a sink (`exit`, `trap`, `raise`) with the log `l`. Its end is the sink's
  flow (`EndRel`) read at the function's result arity (`exitFlow`), keeping the store
  (`endOfFlowS`);
* a Wasm function whose body runs to a pending tail call (`TailL`, made at the function's frame):
  the log, then the tail call `SCall.mk a' args s₁ b s₂` with its answer, the end read from the
  answer (`tailAnsS`);
* a host function: one host call, as in `wasmHOpenXPS`.

`cfgEvFunXPS := Shape.close cfgHOpenXPS`: the closure resolves internal calls (and tail calls)
through functions run on the CFG machine. Theorems in `Silmaril.Wasm.Cfg.CfgSession.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgSession

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHShapeS SCall endOfFlowS tailAnsS exitFlow resFlow wasmHostSig)

variable {H : Type}

/-- **The functions of a store, Wasm bodies run on the logged CFG machine**, host functions as
imports, traps keeping the store. -/
def cfgHOpenXPS : (wasmHShapeS H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (st : MState H)
      (bfl fl : Flow) (l : List (SCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      st.node.IsSink ∧ EndRel st (st.store, st.frame, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ x = (l, endOfFlowS fl st.store)) ∨
    (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (st : MState H)
      (s₁ s₂ : Store H) (f₂ : Frame) (a' n : Nat) (args : List Val)
      (b : (List Val ⊕ Nat) ⊕ PUnit.{1}) (l l' : List (SCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      TailL fn.body st l' (s₁, f₂, .tail a' args n) ∧
      x = ((l ++ l') ++ [SCall.mk a' args s₁ b s₂], tailAnsS rs.length n b s₂)) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlowS fl s'))}

/-- **The CFG session closure**: internal calls resolved through functions run on the CFG
machine. -/
def cfgEvFunXPS :
    AFun (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  fun s p => Shape.close cfgHOpenXPS p.1 s p.2

end Silmaril.Wasm.Cfg.CfgSession
