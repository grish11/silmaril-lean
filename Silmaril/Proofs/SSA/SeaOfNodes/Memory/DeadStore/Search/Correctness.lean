module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Proofs

open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {past : List (List ValueSort)} {version : Nat}
variable {facts : Certificate args} {removeVersion overwrite : Nat}

private theorem findOverwrite_sound (body : Body args past version)
    (found : findOverwrite facts body = some overwrite) :
    version < overwrite ∧ noReadUntil facts overwrite body = true := by
  induction body with
  | ret => cases found
  | load _ address rest ih =>
    by_cases passes : (!facts.matches address && facts.covers address) = true
    · have later : findOverwrite facts rest = some overwrite := by
        simpa only [findOverwrite, ite_eq_left passes] using found
      obtain ⟨strict, checked⟩ := ih later
      exact ⟨strict, by simp [noReadUntil, passes, checked]⟩
    · simp [findOverwrite, passes] at found
  | @store _ version _ address _ rest ih =>
    by_cases matched : facts.matches address = true
    · have chosen : version + 1 = overwrite := Option.some.inj
        (by simpa only [findOverwrite, ite_eq_left matched] using found)
      subst overwrite
      exact ⟨Nat.lt_succ_self _, by simp [noReadUntil, matched]⟩
    · have later : findOverwrite facts rest = some overwrite := by
        simpa only [findOverwrite, ite_eq_right matched] using found
      obtain ⟨strict, checked⟩ := ih later
      exact ⟨Nat.lt_trans (Nat.lt_succ_self _) strict,
        by simp [noReadUntil, Nat.ne_of_lt strict, checked]⟩

private theorem findAfter_sound (body : Body args past version)
    (found : findAfter removeVersion facts body = some overwrite) :
    removeVersion < overwrite ∧
      ∃ rewritten, rewriteAt ⟨removeVersion, overwrite⟩ facts body = some rewritten := by
  induction body with
  | ret => cases found
  | load memory address rest ih =>
    obtain ⟨strict, rewritten, checked⟩ := ih (by simpa only [findAfter] using found)
    exact ⟨strict, .load memory address rewritten, by simp [rewriteAt, checked]⟩
  | @store _ version memory address value rest ih =>
    by_cases here : version + 1 = removeVersion
    · by_cases matched : facts.matches address = true
      · have later : findOverwrite facts rest = some overwrite := by
          simpa only [findAfter, ite_eq_left here, ite_eq_left matched] using found
        obtain ⟨strict, checked⟩ := findOverwrite_sound rest later
        refine ⟨by simpa only [here] using strict, reindexMemory rest version, ?_⟩
        simp [rewriteAt, here, matched, checked]
      · simp [findAfter, here, matched] at found
    · have later : findAfter removeVersion facts rest = some overwrite := by
        simpa only [findAfter, ite_eq_right here] using found
      obtain ⟨strict, rewritten, checked⟩ := ih later
      exact ⟨strict, .store memory address value rewritten, by simp [rewriteAt, here, checked]⟩

theorem discover_sound {graph : Graph args} {candidate : Candidate}
    (found : discover graph removeVersion facts = some candidate) :
    candidate.removeVersion = removeVersion ∧ removeVersion < candidate.overwriteVersion ∧
      ∃ rewritten, Memory.DeadStore.rewriteWith graph candidate facts = some rewritten := by
  obtain ⟨_, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨rfl, findAfter_sound graph selected⟩

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Proofs
