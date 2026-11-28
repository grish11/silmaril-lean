module

public import Silmaril.Wasm.Component.SyncImportITree.Defs
public import Silmaril.Wasm.Component.Reference.HostMap.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

/-! # Reference dispatcher cuts for ready synchronous imports -/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Component.SyncImportITree

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Runtime hiding Thread
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH)
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread ofFlat profile resumeResult)

variable {c : SimpleI} {o : GrowOracle} {σ : Type}

/-- Rename the Core host code of the reference activation to import indices. -/
def refCursor (M : Config (core3P (profile o)) σ) (t : Thread) : Cursor :=
  (Store.mapH trampIdx M.store.core, t)

/-- A focused Core activation at a synchronous, optionless `SimpleI` lower in instance zero.
The arguments are flat at the Core boundary and lift to the typed component question. -/
structure ReferenceCut (M : Config (core3P (profile o)) σ) (m : Question c.imports) where
  owner : Option ThreadId
  thread : Thread
  returnTo : List Flat → P (core3P (profile o)) σ (Ret (core3P (profile o)))
  frames : List (Seg (core3P (profile o)) σ)
  resumers : List (Activation (core3P (profile o)) σ)
  flatArgs : List Flat
  focused : M.ctl = ⟨owner, .core thread returnTo, frames⟩ :: resumers
  status : (core3P (profile o)).status M.store.core thread =
    .callout (.lowered ⟨m.index.val⟩ (witFt c.imports[m.index].2) {} ⟨0⟩) flatArgs
  flatTypes : flatArgs.map (·.type) = ValTy.flatList c.imports[m.index].2.params
  lifted : liftArgs c.imports[m.index].2.params flatArgs = some m.args.val

namespace ReferenceCut

variable {M : Config (core3P (profile o)) σ} {m : Question c.imports}

/-- The machine after `coreCallout` parks exactly this Core segment and dispatches the lower. -/
def parked (cut : ReferenceCut M m) (host : Host (core3P (profile o)) σ) :
    Config (core3P (profile o)) σ :=
  { M with ctl := ⟨cut.owner,
      .prog (host.dispatch (.hostCallout (.lowered ⟨m.index.val⟩ (witFt c.imports[m.index].2) {} ⟨0⟩)
        cut.flatArgs)), .core cut.thread cut.returnTo :: cut.frames⟩ :: cut.resumers }

/-- The tree's residual cursor after a typed reply or an explicit game trap reply. -/
def resume (cut : ReferenceCut M m) (a : m.Answer) : Cursor :=
  let s := (refCursor M cut.thread).1
  (s, resumeResult s cut.thread (match a with
    | none => .trap
    | some vs => .values ((lowerArgs c.imports[m.index].2.results vs.val).map ofFlat)))

/-- The dispatcher entry checks and host binding for an unlocked ready callout. -/
structure CanDispatch (cut : ReferenceCut M m) : Prop where
  unlocked : M.store.lockdown = false
  entry : calloutEntry M.store cut.owner
    (.lowered ⟨m.index.val⟩ (witFt c.imports[m.index].2) {} ⟨0⟩) = none
  mayLeave : ∃ st, ArenaField.insts.get? M.store ⟨0⟩ = some st ∧ st.mayLeave = true
  hostFunc : ArenaField.funcs.get? M.store ⟨m.index.val⟩ =
    some (.host (witFt c.imports[m.index].2) ⟨m.index.val⟩)

end ReferenceCut

end Silmaril.Wasm.Component.SyncImportITree
