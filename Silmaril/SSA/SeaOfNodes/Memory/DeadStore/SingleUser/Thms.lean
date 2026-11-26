module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser

open RVSDG (Tuple)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {version : Nat}

/-- Eligibility in the initialized linear profile is exactly a
same-pointer adjacent pair and the single actual overwrite use. -/
theorem rewrite_exists_iff (graph : Graph args) (version : Nat) :
    (∃ rewritten, rewrite graph version = some rewritten) ↔
      usersOf version graph = [.store (version + 1)] ∧
        ∃ address, adjacentAddress version graph = some address :=
  Proofs.rewrite_exists_iff graph version

/-- Success identifies the actual Store user and replays the original
rewrite with an empty reader certificate. -/
theorem rewrite_checked (success : rewrite graph version = some rewritten) :
    usersOf version graph = [.store (version + 1)] ∧
      ∃ address, adjacentAddress version graph = some address ∧
        DeadStore.rewriteWith graph ⟨version, version + 1⟩ ⟨address, []⟩ = some rewritten :=
  Proofs.rewrite_checked success

/-- Every ordered Load reads the same word in both graphs, including Loads
whose words are unused by Return. Out-of-range Load ordinals agree too. -/
theorem rewrite_readAt (success : rewrite graph version = some rewritten) (index : Nat)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    readAt rewritten index input PUnit.unit initial = readAt graph index input PUnit.unit initial :=
  Proofs.rewrite_readAt success index input initial

theorem rewrite_denote (success : rewrite graph version = some rewritten)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    rewritten.denote input initial = graph.denote input initial := by
  obtain ⟨_, _, _, replay⟩ := rewrite_checked success
  exact DeadStore.rewriteWith_denote replay input (by simp [Forwarding.Disjoint.Certificate.Valid]) initial

/-- The explicit memory-edge rules agree on the returned word and full heap. -/
theorem rewrite_returns_iff (success : rewrite graph version = some rewritten)
    (input : Tuple (Val cells) args) (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewrite_denote success]

/-- Run the two actual emitted MemRef blocks at any typed invocation and
initialized buffer. The observation includes the returned word and every cell. -/
theorem rewrite_observe (success : rewrite graph version = some rewritten)
    (input : Tuple (Val cells) args) (initial : Buffer cells) :
    observe rewritten input initial = observe graph input initial := by
  rw [lower_run, lower_run, rewrite_denote success]

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser
