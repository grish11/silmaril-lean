module

public import Silmaril.Wasm.Cfg.CfgClosure.Defs
public import Silmaril.Wasm.Cfg.MachineLDiv.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXPBack.Thms
import Silmaril.Proofs.Wasm.Cfg.CfgClosure

@[expose] public section

/-!
# The self-contained recursive CFG closure: theorems (H3)

Proofs in `Silmaril.Proofs.Wasm.Cfg.CfgClosure` and `…CfgClosureAns`.

**The native instance** (by definition): `MachineLDiv`'s divergence is the generic one at the
native answers `CloseOk closedCallXP` and native callee divergence `FunDivXP` (`stepK_eq`,
`infK_eq`, `calleeDivK_eq`, `tailDivK_eq`, `mDivL_eq`, `funDivL_eq`, `mLogDivL_eq`). The theorems
of `MachineLDiv` and `CfgSession` keep their statements over that instance.

**The CFG instance equals the native one** (no hypothesis):

* `cfgAns_eq`: the CFG closure's host-free answers are exactly `CloseOk closedCallXP`. One way is
  `MachineLClose.closeOk_of_session`; the other (`session_of_closeOk`) is new: every
  `closedCallXP` answer (values at the callee's result arity, an uncaught exception, a trap) is a
  behaviour of the store-retaining session closure with the empty log, in the answer's store.
* `funDivXP_of_post`: every post-fixpoint `R ≤ FunDivLG (CloseOk closedCallXP) R` is below
  `FunDivXP`, by native coinduction. `cfgFunDiv_eq`: the CFG-defined greatest fixpoint
  `cfgFunDiv` is `FunDivXP`.
* `ldlcfgC_eq`, `cfgEvFunDC_eq`: the CFG-closed logged divergence and divergent closure are
  `CfgSession`'s. **`cfgSessionTripleC_eq`**: the self-contained CFG session triple is the session
  triple `Abstract.sessionTripleXP`.

**Core** (deterministic profile; the hypotheses of `Abstract.invoke_diverges_iff_funDivXP_of` and
`Abstract.wasmEvFunXPS_*_iff`, the typed invocation and store facts, which are assumed here, not
derived from module validation): `cfgFunDiv_iff_diverges` (host-free Core divergence of the
invocation), `cfgAns_trap_iff`, `cfgAns_vals_iff`, `cfgAns_throw_iff` (host-free Core runs to a
trap, values, an exception, each in the answer's store).
-/

namespace Silmaril.Wasm.Cfg.CfgClosure

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (FunDivXP)

variable {H : Type}

/-! ## The native instance -/

theorem stepK_eq : (StepK : Expr → MState H → MState H → Prop) =
    StepKG (CloseOk closedCallXP) := rfl

theorem infK_eq : (InfK : Expr → MState H → Prop) = InfKG (CloseOk closedCallXP) := rfl

theorem calleeDivK_eq : (CalleeDivK : Expr → MState H → Prop) =
    CalleeDivKG (CloseOk closedCallXP) FunDivXP := rfl

theorem tailDivK_eq : (TailDivK : Expr → MState H → Prop) =
    TailDivKG (CloseOk closedCallXP) FunDivXP := rfl

theorem mDivL_eq : (MDivL : Expr → MState H → Prop) =
    MDivLG (CloseOk closedCallXP) FunDivXP := rfl

theorem funDivL_eq : (FunDivL : Store H → Nat → List Val → Prop) =
    FunDivLG (CloseOk closedCallXP) FunDivXP := rfl

theorem mLogDivL_eq : (MLogDivL : Expr → MState H → List (SCall H) → Prop) =
    MLogDivLG (CloseOk closedCallXP) FunDivXP := rfl

/-! ## The CFG instance -/

/-- **A `closedCallXP` answer is a host-free session behaviour**: values at the callee's result
arity, an uncaught exception, or a trap, in the answer's store. -/
theorem session_of_closeOk {s s₂ : Store H} {g : Nat} {args : List Val}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}} (h : CloseOk closedCallXP (Abstract.SCall.mk g args s b s₂)) :
    (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s₂) ∈ Abstract.wasmEvFunXPS s (g, args) :=
  Proofs.CfgClosureAns.session_of_closeOk h

/-- **The CFG closure's call answers are the native closed oracle's.** -/
theorem cfgAns_eq : (cfgAns : SCall H → Prop) = CloseOk closedCallXP :=
  Proofs.CfgClosure.cfgAns_eq

/-- **Every post-fixpoint of machine frame divergence is native frame divergence.** -/
theorem funDivXP_of_post {R : Store H → Nat → List Val → Prop}
    (hR : ∀ s a args, R s a args → FunDivLG (CloseOk closedCallXP) R s a args) :
    ∀ s a args, R s a args → FunDivXP s a args :=
  Proofs.CfgClosure.le_funDivXP hR

/-- **The CFG closure's callee divergence is native frame divergence.** -/
theorem cfgFunDiv_eq : (cfgFunDiv : Store H → Nat → List Val → Prop) = FunDivXP :=
  Proofs.CfgClosure.cfgFunDiv_eq

/-- **`cfgFunDiv` is a fixpoint**: a call diverges exactly when it diverges at its frame on the
machine, by CFG answers, into diverging callees. -/
theorem cfgFunDiv_iff {s : Store H} {a : Nat} {args : List Val} :
    cfgFunDiv s a args ↔ FunDivLG cfgAns cfgFunDiv s a args := by
  rw [cfgAns_eq, cfgFunDiv_eq]
  exact MachineL.funDiv_iff

/-- **The CFG-closed logged divergence is `CfgSession`'s.** -/
theorem ldlcfgC_eq :
    (LDLcfgC : (Abstract.wasmHShape H).self.Op → List (Abstract.HCall H) → Prop) = LDLcfg :=
  Proofs.CfgClosure.ldlcfgC_eq

/-- **The CFG-closed divergent closure is `CfgSession`'s.** -/
theorem cfgEvFunDC_eq : (cfgEvFunDXPC : AFun (Abstract.wasmHostSig H) (Store H)
    (Nat × List Val) (List Val ⊕ Nat)) = cfgEvFunDXP :=
  Proofs.CfgClosure.cfgEvFunDC_eq

/-- **The self-contained CFG session triple is the session triple.** -/
theorem cfgSessionTripleC_eq :
    (cfgSessionTripleC : ObsTriple (Abstract.wasmHostSig H) (Store H) (Nat × List Val)
      ((List Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.sessionTripleXP :=
  Proofs.CfgClosure.cfgSessionTripleC_eq

/-! ## Core -/

section Core

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **CFG callee divergence is host-free Core divergence** of a typed invocation. -/
theorem cfgFunDiv_iff_diverges {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) :
    cfgFunDiv s a vs ↔
      Diverges (profile o) (fun _ _ _ _ => False) (invoke s a vs) := by
  rw [cfgFunDiv_eq]
  exact (Abstract.invoke_diverges_iff_funDivXP_of hs hok hS hts).symm

theorem consistent_nil :
    (Abstract.coreHostRel host).Consistent ([] : List (Call (Abstract.wasmHostSig H))) :=
  fun _ h => nomatch h

/-- **A CFG trap answer is a host-free Core run to a trap** in exactly its store. -/
theorem cfgAns_trap_iff (hT : Abstract.HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    cfgAns (Abstract.SCall.mk a vs s (.inr ()) s₂) ↔
      Abstract.EvRun (profile o) host (invoke s a vs) [] ⟨s₂, {}, [.trap]⟩ := by
  show _ ∈ cfgEvFunXPS s (a, vs) ↔ _
  rw [CfgSession.cfgEvFun_eq, ← Abstract.wasmEvFunXPS_trap_iff hT hH hE hs hS hts hok]
  exact ⟨fun h => ⟨h, consistent_nil⟩, And.left⟩

/-- **A CFG answer by values is a host-free Core run to those values** in exactly its store. -/
theorem cfgAns_vals_iff (hT : Abstract.HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs ws : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    cfgAns (Abstract.SCall.mk a vs s (.inl (.inl ws)) s₂) ↔
      Abstract.EvRun (profile o) host (invoke s a vs) [] ⟨s₂, {}, vals ws⟩ := by
  show _ ∈ cfgEvFunXPS s (a, vs) ↔ _
  rw [CfgSession.cfgEvFun_eq, ← Abstract.wasmEvFunXPS_vals_iff hT hH hE hs hS hts hok]
  exact ⟨fun h => ⟨h, consistent_nil⟩, And.left⟩

/-- **A CFG answer by an exception is a host-free Core run throwing it** in exactly its store. -/
theorem cfgAns_throw_iff (hT : Abstract.HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat}
    (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) :
    cfgAns (Abstract.SCall.mk a vs s (.inl (.inr t)) s₂) ↔
      Abstract.EvRun (profile o) host (invoke s a vs) [] ⟨s₂, {}, throwing t⟩ := by
  show _ ∈ cfgEvFunXPS s (a, vs) ↔ _
  rw [CfgSession.cfgEvFun_eq, ← Abstract.wasmEvFunXPS_throw_iff hT hH hE hs hS hts hok]
  exact ⟨fun h => ⟨h, consistent_nil⟩, And.left⟩

end Core

end Silmaril.Wasm.Cfg.CfgClosure
