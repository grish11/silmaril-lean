module

public import Silmaril.Wasm.Cfg.Maximal.Defs
public import Silmaril.Wasm.Cfg.Variant.Thms
import Silmaril.Proofs.Wasm.Cfg.Maximal

@[expose] public section

/-!
# Maximal basic blocks: theorems

- `canMerge_functional`, `canMerge_inj`, `canMerge_not_entry` (`Variant`): each block merges
  into at most one successor, each block is merged into by at most one predecessor, and the entry
  is never merged into. So the merges split the blocks into disjoint chains, each starting at a
  block that is not a merge target.
- `mem_maxFlow`: an edge of a member is kept in the contracted graph exactly when it is an AE edge
  and not a merged fall-through; `internal_iff` says what a merged fall-through is.
- `mem_maxHandler`: the handler edges are kept exactly.
- `internal_only`: a merged fall-through is its block's only AE edge, so dropping it removes no
  other edge of that block.
-/

namespace Silmaril.Wasm.Cfg

/-- A block merges into at most one successor. -/
theorem canMerge_functional {body : Expr} {b c c' : BlockId} (h : canMerge body b c = true)
    (h' : canMerge body b c' = true) : c' = c :=
  Target.block.inj ((canMerge_succ h (.block c')).1 ((canMerge_succ h' (.block c')).2 rfl))

/-- At most one block merges into a given block. -/
theorem canMerge_inj {body : Expr} {b b' c : BlockId} (h : canMerge body b c = true)
    (h' : canMerge body b' c = true) : b' = b := by
  obtain ⟨s', hs', hm⟩ := (canMerge_succ h' (.block c)).2 rfl
  exact canMerge_pred h hs' (Or.inl hm)

/-- **The kept AE edges**: exactly the AE edges that are not merged fall-throughs. -/
theorem mem_maxFlow (body : Expr) (b : BlockId) (t : Target) :
    (b, t) ∈ maxFlow body ↔ EdgeAE body b t ∧ internal body b t = false :=
  Proofs.Maximal.mem_maxFlow body b t

/-- **The kept handler edges**: all of them. -/
theorem mem_maxHandler (body : Expr) (b : BlockId) (t : Target) :
    (b, t) ∈ maxHandler body ↔ HandlerEdge body b t :=
  Proofs.Maximal.mem_maxHandler body b t

/-- What a merged fall-through is. -/
theorem internal_iff (body : Expr) (b : BlockId) (t : Target) :
    internal body b t = true ↔ ∃ c, t = .block c ∧ canMerge body b c = true :=
  Proofs.Maximal.internal_iff body b t

/-- A merged fall-through is its block's only AE edge. -/
theorem internal_only {body : Expr} {b : BlockId} {t : Target} (h : internal body b t = true)
    (t' : Target) : EdgeAE body b t' ↔ t' = t := by
  obtain ⟨c, rfl, hc⟩ := (internal_iff body b t).1 h
  exact canMerge_succ hc t'

end Silmaril.Wasm.Cfg
