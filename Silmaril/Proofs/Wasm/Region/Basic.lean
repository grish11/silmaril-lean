module

public import Silmaril.Wasm.Region.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.Proofs
open Silmaril.Semantics.Region

theorem candidate_covers (body : Expr) (b : Cfg.BlockId) (s : Cfg.Segment) (t : Cfg.Target)
    (edge : t ∈ Cfg.succOf body b s ∨ t ∈ Cfg.effectSucc body b s) :
    (candidateTargets body b s).Allows t := by
  dsimp only [candidateTargets]
  split
  · trivial
  · exact List.mem_toFinset.mpr (List.mem_append.mpr edge)

end Silmaril.Wasm.Region.Proofs
