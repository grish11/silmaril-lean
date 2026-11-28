module

public import Silmaril.Wasm.Component.Reference.SyncImportCut.Defs
public import Silmaril.Wasm.Component.SyncImportITree.Thms
import Silmaril.Proofs.Wasm.Component.Reference.SyncImportCut

public section

namespace Silmaril.Wasm.Component.SyncImportITree.ReferenceCut

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Runtime hiding Thread
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread profile)

variable {c : SimpleI} {o : GrowOracle} {σ : Type}
  {r : Ready c} {q : Question (exportIface c)} {f : r.inst.F.Op}
  {M : Config (core3P (profile o)) σ} {m : Question c.imports} {prof : ProfileKind}

/-- A stock Core-only machine prefix ending at a typed lower gives the tree's visible
request via `tree_request`. The next dispatcher step saves the same thread and continuation
as a `Seg.core`. -/
theorem request {host : Host (core3P (profile o)) σ} {before : Config (core3P (profile o)) σ}
    {t : Thread} {tr : List (Label (core3P (profile o)) σ)}
    (cut : ReferenceCut M m)
    (focus : before.ctl = ⟨cut.owner, .core t cut.returnTo, cut.frames⟩ :: cut.resumers)
    (run : Steps prof host.hr host.dispatch before tr M) (internal : ∀ l ∈ tr, l = .core) :
    ReachesFront o r q f (refCursor before t) (.request m cut.resume) ∧
    Step prof host.hr host.dispatch M .tau (cut.parked host) :=
  Silmaril.Proofs.Wasm.Component.Reference.SyncImportCut.request cut focus run internal

/-- With a typed answer from the stock answering host, the dispatcher services
`on_start` and `on_resolve` and returns flat results to the parked segment.
The next step restores its continuation at exactly the ITree reply cursor. -/
theorem answer (r : Ready c)
    {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)} {s' : σ}
    (cut : ReferenceCut M m) (ready : cut.CanDispatch)
    (a : Values c.imports[m.index].2.results)
    (reply : g M.host ⟨m.index.val⟩ (m.args.val.map toRefVal) = some (a.val.map toRefVal, s')) :
    let host := answerHostS (profile o) g
    ∃ tr resolved next,
      Steps prof host.hr host.dispatch (cut.parked host) tr resolved ∧
      resolved.ctl = ⟨cut.owner, .prog (.pure (.flat (lowerArgs c.imports[m.index].2.results a.val))),
        .core cut.thread cut.returnTo :: cut.frames⟩ :: cut.resumers ∧
      Step prof host.hr host.dispatch resolved .tau next ∧
      next.host = s' ∧ next.store.core = M.store.core ∧
      next.ctl = ⟨cut.owner, .core (cut.resume (some a)).2 cut.returnTo, cut.frames⟩ :: cut.resumers :=
  Silmaril.Proofs.Wasm.Component.Reference.SyncImportCut.answer r cut ready a reply

/-- When the stock answering host refuses a typed call, the dispatcher reaches a trap
that locks down the store and discards the running control chain. -/
theorem refuses (r : Ready c)
    {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)}
    (cut : ReferenceCut M m) (ready : cut.CanDispatch)
    (reply : g M.host ⟨m.index.val⟩ (m.args.val.map toRefVal) = none) :
    let host := answerHostS (profile o) g
    ∃ tr pre reason,
      Steps prof host.hr host.dispatch (cut.parked host) tr pre ∧
      Step prof host.hr host.dispatch pre (.trap reason) (trapCfg pre) :=
  Silmaril.Proofs.Wasm.Component.Reference.SyncImportCut.refuses r cut ready reply

end Silmaril.Wasm.Component.SyncImportITree.ReferenceCut
