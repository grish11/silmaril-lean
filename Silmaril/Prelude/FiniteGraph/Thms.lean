module

public import Silmaril.Prelude.FiniteGraph.Defs
import Silmaril.Proofs.Prelude.FiniteGraph

/-!
# Acyclicity of finite dependency graphs: Kahn's algorithm is sound and complete

* `kahn_sound`: when `kahn` succeeds, `krank` ranks the graph and is below the number
  of nodes;
* `kahn_complete`: any ranking makes `kahn` succeed (the pending node of least rank is
  always ready);
* `kahn_iff`: `kahn deps nodes = true ↔ Acyclic deps nodes`;
* `acyclic_iff_edges`: the same acyclicity stated for an edge relation `E` whose edges
  are exactly the `deps` edges between nodes.
-/

@[expose] public section

namespace Silmaril.FiniteGraph

variable {α : Type} [DecidableEq α] (deps : α → List α)

theorem kahn_of_any {rest : List α} (h : rest.any (ready deps rest) = true) :
    kahn deps rest = kahn deps (nextRound deps rest) :=
  Proofs.Prelude.FiniteGraph.kahn_of_any deps h

theorem kahn_of_not_any {rest : List α} (h : ¬ rest.any (ready deps rest) = true) :
    kahn deps rest = rest.isEmpty :=
  Proofs.Prelude.FiniteGraph.kahn_of_not_any deps h

theorem krank_of_any {rest : List α} (h : rest.any (ready deps rest) = true) (a : α) :
    krank deps rest a =
      if ready deps rest a then 0 else krank deps (nextRound deps rest) a + 1 :=
  Proofs.Prelude.FiniteGraph.krank_of_any deps h a

theorem not_mem_of_ready {rest : List α} {a b : α} (hr : ready deps rest a = true)
    (hb : b ∈ deps a) : b ∉ rest :=
  Proofs.Prelude.FiniteGraph.not_mem_of_ready deps hr hb

theorem mem_nextRound {rest : List α} {a : α} :
    a ∈ nextRound deps rest ↔ a ∈ rest ∧ ready deps rest a = false :=
  Proofs.Prelude.FiniteGraph.mem_nextRound deps

theorem nextRound_subset {rest : List α} {a : α} (h : a ∈ nextRound deps rest) :
    a ∈ rest :=
  Proofs.Prelude.FiniteGraph.nextRound_subset deps h

/-- One round preserves rankedness backwards: if the pending nodes are ranked by
`krank`, so are the nodes before the round. -/
theorem ranked_step {rest : List α} (h : rest.any (ready deps rest) = true)
    (ih : Ranked deps (nextRound deps rest) (krank deps (nextRound deps rest))) :
    Ranked deps rest (krank deps rest) :=
  Proofs.Prelude.FiniteGraph.ranked_step deps h ih

/-- One round preserves the bound `krank < length` backwards. -/
theorem bound_step {rest : List α} (h : rest.any (ready deps rest) = true)
    (ih : ∀ a ∈ nextRound deps rest, krank deps (nextRound deps rest) a <
      (nextRound deps rest).length) :
    ∀ a ∈ rest, krank deps rest a < rest.length :=
  Proofs.Prelude.FiniteGraph.bound_step deps h ih

/-- When `kahn` succeeds, `krank` ranks the graph and stays below the number of
nodes. -/
theorem kahn_sound (rest : List α) (hk : kahn deps rest = true) :
    Ranked deps rest (krank deps rest) ∧ ∀ a ∈ rest, krank deps rest a < rest.length :=
  Proofs.Prelude.FiniteGraph.kahn_sound deps rest hk

omit [DecidableEq α] in
theorem exists_min (r : α → Nat) : ∀ (l : List α), l ≠ [] → ∃ m ∈ l, ∀ x ∈ l, r m ≤ r x :=
  Proofs.Prelude.FiniteGraph.exists_min r

omit [DecidableEq α] in
theorem ranked_mono {nodes nodes' : List α} {r : α → Nat} (hR : Ranked deps nodes r)
    (hsub : ∀ a ∈ nodes', a ∈ nodes) : Ranked deps nodes' r :=
  Proofs.Prelude.FiniteGraph.ranked_mono deps hR hsub

theorem ready_of_min {rest : List α} {r : α → Nat} (hR : Ranked deps rest r) {m : α}
    (hm : m ∈ rest) (hmin : ∀ x ∈ rest, r m ≤ r x) : ready deps rest m = true :=
  Proofs.Prelude.FiniteGraph.ready_of_min deps hR hm hmin

/-- Any ranking makes `kahn` succeed. -/
theorem kahn_complete (rest : List α) {r : α → Nat} (hR : Ranked deps rest r) :
    kahn deps rest = true :=
  Proofs.Prelude.FiniteGraph.kahn_complete deps rest hR

theorem kahn_iff (nodes : List α) : kahn deps nodes = true ↔ Acyclic deps nodes :=
  Proofs.Prelude.FiniteGraph.kahn_iff deps nodes

omit [DecidableEq α] in
/-- Acyclicity for an edge relation that has exactly the `deps` edges between nodes. -/
theorem acyclic_iff_edges {nodes : List α} {E : α → α → Prop}
    (hE : ∀ a b, E a b ↔ a ∈ nodes ∧ b ∈ deps a ∧ b ∈ nodes) :
    Acyclic deps nodes ↔ ∃ r : α → Nat, ∀ a b, E a b → r b < r a :=
  Proofs.Prelude.FiniteGraph.acyclic_iff_edges deps hE

/-- A successful `kahn` gives a ranking of the edge relation bounded by the number of
nodes. -/
theorem kahn_bounded_edges {nodes : List α} {E : α → α → Prop}
    (hE : ∀ a b, E a b ↔ a ∈ nodes ∧ b ∈ deps a ∧ b ∈ nodes) (hk : kahn deps nodes = true) :
    ∃ r : α → Nat, (∀ a b, E a b → r b < r a) ∧ ∀ a ∈ nodes, r a < nodes.length :=
  Proofs.Prelude.FiniteGraph.kahn_bounded_edges deps hE hk

end Silmaril.FiniteGraph
