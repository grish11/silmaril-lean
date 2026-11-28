module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Proofs

open RVSDG (Origin Port Tuple)
open Memory.Forwarding (originKey_injective)

variable {args : List ValueSort} {past : List (List ValueSort)} {live : Nat}

private theorem adjacent_replay {version : Nat} {address : Port args .address} (body : Body args past live)
    (accepted : adjacentAddress version body = some address) :
    ∃ rewritten, rewriteAt ⟨version, version + 1⟩ ⟨address, []⟩ body = some rewritten := by
  induction body with
  | ret => contradiction
  | load memory reader rest ih =>
    obtain ⟨rewritten, replay⟩ := ih accepted
    exact ⟨.load memory reader rewritten, by simp [rewriteAt, replay]⟩
  | @store scope live memory earlier word rest ih =>
    by_cases nominated : live + 1 = version
    · subst version
      cases earlier with
      | output => cases rest <;> simp [adjacentAddress] at accepted
      | arg first =>
        cases rest with
        | ret => simp [adjacentAddress] at accepted
        | load => simp [adjacentAddress] at accepted
        | store laterMemory later retainedWord suffix =>
          cases later with
          | output => simp [adjacentAddress] at accepted
          | arg second =>
            by_cases same : first.index = second.index
            · have anchor : first = address := by simpa [adjacentAddress, same] using accepted
              have pointers : (Origin.arg first : Origin args scope .address) = .arg second :=
                originKey_injective (congrArg Sum.inl same)
              have equal := Origin.arg.inj pointers
              subst second
              subst address
              exact ⟨reindexMemory (.store laterMemory (.arg first) retainedWord suffix) live,
                by simp [rewriteAt, noReadUntil, Forwarding.Disjoint.Certificate.matches]⟩
            · simp [adjacentAddress, same] at accepted
    · have later : adjacentAddress version rest = some address := by
        simpa only [adjacentAddress, ite_eq_right nominated] using accepted
      obtain ⟨rewritten, replay⟩ := ih later
      exact ⟨.store memory earlier word rewritten, by simp [rewriteAt, nominated, replay]⟩

theorem rewrite_checked {graph rewritten : Graph args} {version : Nat}
    (success : rewrite graph version = some rewritten) :
    usersOf version graph = [.store (version + 1)] ∧
      ∃ address, adjacentAddress version graph = some address ∧
        DeadStore.rewriteWith graph ⟨version, version + 1⟩ ⟨address, []⟩ = some rewritten := by
  unfold rewrite at success
  split at success
  next unique =>
    obtain ⟨address, selected, replay⟩ := Option.bind_eq_some_iff.mp success
    exact ⟨unique, address, selected, replay⟩
  next => contradiction

theorem rewrite_exists_iff (graph : Graph args) (version : Nat) :
    (∃ rewritten, rewrite graph version = some rewritten) ↔
      usersOf version graph = [.store (version + 1)] ∧
        ∃ address, adjacentAddress version graph = some address := by
  constructor
  · rintro ⟨rewritten, checked⟩
    obtain ⟨users, address, pair, _⟩ := rewrite_checked checked
    exact ⟨users, address, pair⟩
  · rintro ⟨users, address, pair⟩
    obtain ⟨rewritten, replay⟩ := adjacent_replay graph pair
    exact ⟨rewritten, by simpa [rewrite, users, pair, rewriteWith] using replay⟩

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Proofs
