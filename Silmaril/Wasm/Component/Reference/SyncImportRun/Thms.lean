module

public import Silmaril.Wasm.Component.Reference.SyncImportRun.Defs
public import Silmaril.Wasm.Component.Reference.SyncImportCut.Thms
import Silmaril.Proofs.Wasm.Component.Reference.SyncImportRun

public section

namespace Silmaril.Wasm.Component.SyncImportITree

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- A stock successful call of a freshly instantiated, start-free `SimpleI` export has a
matching ITree path. Each answered import contributes its typed question and reply in order.
The path returns the same values and the terminal Core store, with host code renamed by
`trampIdx`. The import replies thread the host state of the actual run. -/
theorem sees_of_reference_return {c : SimpleI} (r : Ready c) (wired : c.Inst)
    (q : Question (exportIface c)) {o : GrowOracle} {prof : ProfileKind} {σ : Type}
    {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)}
    (typedHost : c.HostOkS g) {s₀ : σ} {ready finished : Config (core3P (profile o)) σ}
    {inst : InstId} {exports : List (String × FuncId)} {f : FuncId} {rs : List Reference.Val}
    (init : let h := answerHostS (profile o) g
      Instantiates prof h.hr h.dispatch (Config.init (hostFuncs 0 c.imports CStore.empty) s₀)
        c.toRef (importArgs c.imports) ready inst exports)
    (lookup : exports.lookup (exportIface c)[q.index].1 = some f)
    (run : let h := answerHostS (profile o) g
      Calls prof h.hr h.dispatch ready ⟨0⟩ f (q.args.val.map toRefVal) finished
        (.resolved (some rs))) :
    ∃ (a : Values (exportIface c)[q.index].2.results) (cs : List (Call (signature c.imports))),
      a.val.map toRefVal = rs ∧ HostReplies (c := c) g s₀ cs finished.host ∧
      Sees ((body o r q).run ⟨r.inst.store⟩).run cs
        (.reply (some a) (Store.mapH trampIdx finished.store.core)) :=
  Silmaril.Proofs.Wasm.Component.Reference.SyncImportRun.sees_of_reference_return
    r wired q typedHost init lookup run

end Silmaril.Wasm.Component.SyncImportITree
