module

public import Silmaril.Wasm.Region.Defs
import Silmaril.Proofs.Wasm.Region.Basic

@[expose] public section
namespace Silmaril.Wasm.Region
open Silmaril.Semantics.Region

/-- The adapter preserves every existing syntactic control and effect edge.
This is deliberately a graph theorem, not an execution soundness theorem. -/
theorem candidate_covers (body : Expr) (b : Cfg.BlockId) (s : Cfg.Segment) (t : Cfg.Target)
    (edge : t ∈ Cfg.succOf body b s ∨ t ∈ Cfg.effectSucc body b s) :
    (candidateTargets body b s).Allows t := Proofs.candidate_covers body b s t edge

theorem rawMap_correct {bodySize : Nat → Nat}
    {decodesAt : DecodedLabel → Silmaril.Machine.Region.Range → Prop}
    (map : ValidatedByteMap bodySize decodesAt) (m : ByteMapEntry) (hm : m ∈ map.entries) :
    decodesAt m.decoded m.bytes := map.correct m hm

/-- Calls preserve uncertainty instead of certifying an unproved resumption. -/
theorem call_unknown : candidateTargets [.call ⟨0⟩] ⟨[], 0⟩ ⟨[.call ⟨0⟩], none⟩ = .top := rfl
theorem trap_distinct : candidateTargets [.unreachable] ⟨[], 0⟩ ⟨[], some .unreachable⟩ =
    .finite {.trap} := rfl
theorem return_distinct : candidateTargets [.return_] ⟨[], 0⟩ ⟨[], some .return_⟩ =
    .finite {.exit} := rfl

end Silmaril.Wasm.Region
