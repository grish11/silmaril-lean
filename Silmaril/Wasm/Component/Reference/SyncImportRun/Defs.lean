module

public import Silmaril.Wasm.Component.SyncImportITree.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.SyncImportITree

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Runtime (HostFuncId)

/-- The typed successful imports of one export call, with the answering host's state
threaded through the calls in order. -/
inductive HostReplies {c : SimpleI} {σ : Type}
    (g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)) :
    σ → List (Call (signature c.imports)) → σ → Prop where
  | nil (s : σ) : HostReplies g s [] s
  | cons {s s' s'' : σ} {m : Question c.imports} {a : Values c.imports[m.index].2.results}
      {cs : List (Call (signature c.imports))} :
      g s ⟨m.index.val⟩ (m.args.val.map toRefVal) = some (a.val.map toRefVal, s') →
      HostReplies g s' cs s'' → HostReplies g s (⟨m, some a⟩ :: cs) s''

end Silmaril.Wasm.Component.SyncImportITree
