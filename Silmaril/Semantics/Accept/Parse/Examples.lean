module

public import Silmaril.Semantics.Accept.Parse.Thms

/-!
# Parsing sessions: examples

* `projection_inter_strict`: two relations whose input languages share `[1]` and whose
  intersection is empty: projections do not preserve intersections.
* `chunk_example`: chunks `[1, 2, 3]` then `[4]`; `done` uses `2` and fails (sentinel `0`),
  then uses `2` and succeeds: the second pair relates `[3, 4]`, the slice after the advanced
  cursor, and nothing relates `[1, 2]`.
* `done_twice`: with `doneClears`, a second `done()` relates the empty input.
-/

@[expose] public section

namespace Silmaril.Accept.Parse.Examples

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

theorem projection_inter_strict :
    inputLang ({([1], 0)} : Set (List ℕ × ℕ)) ∩ inputLang {([1], 1)} = {[1]} ∧
      inputLang (({([1], 0)} : Set (List ℕ × ℕ)) ∩ {([1], 1)}) = ∅ := by
  constructor
  · ext w; simp [inputLang]
  · ext w; simp [inputLang]

/-- Sentinel `0`, every other handle resolves to itself; an overrun aborts the session (the
policy of the cursor invariant, `parseRel_slice`). -/
def pol0 : PPolicy ℕ := {sentinel := 0, onOverrun := .sessionTrap}

def ρid : Env ℕ ℕ := some

def tChunk : List (PEv ℕ ℕ) := [.feed [1, 2, 3], .finish 2 0, .feed [4], .finish 2 7]

theorem chunk_example : ([3, 4], 7) ∈ parseRel pol0 {ρid} {tChunk} ∧
    ∀ x, ([1, 2], x) ∉ parseRel pol0 {ρid} {tChunk} := by
  constructor
  · unfold parseRel langOver
    rw [Set.mem_iUnion]
    exact ⟨⟨ρid, rfl⟩, mem_lang.2 ⟨tChunk, rfl, _, _,
      .cons (.feed _) (.cons (.ret (w := [1, 2]) (h := 0) (A := ∅) rfl ⟨by simp, rfl, rfl, rfl⟩
        (by simp [resolve, pol0])) (.cons (.feed _)
          (.cons (.ret (w := [3, 4]) (h := 7) (A := {([3, 4], 7)}) rfl ⟨by simp, rfl, rfl, rfl⟩
            (by simp [resolve, pol0, ρid])) (.nil _)))), by simp⟩⟩
  · intro x hx
    obtain ⟨t, ht, u, n, h, v, he, h1, -, hns, -⟩ :=
      parseRel_slice (pol := pol0) rfl (by simp [pol0]) (fun t ht => by
        rw [Set.mem_singleton_iff] at ht; subst ht
        intro e he; simp [tChunk] at he
        rcases he with rfl | rfl | rfl | rfl <;> simp) hx
    rw [Set.mem_singleton_iff] at ht
    subst ht
    -- the two `finish` positions
    rcases u with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, u⟩⟩⟩⟩ <;> simp [tChunk] at he
    · obtain ⟨-, rfl⟩ := he.2.1
      exact hns rfl
    · obtain ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, -⟩ := he
      simp [fed, consumed] at h1

theorem done_twice : ([], 5) ∈ parseRel pol0 {ρid} {[.append 1, .done 9, .done 5]} := by
  unfold parseRel langOver
  rw [Set.mem_iUnion]
  exact ⟨⟨ρid, rfl⟩, mem_lang.2 ⟨_, rfl, _, _,
    .cons (.append 1) (.cons (.ret (w := [1]) (h := 9) (A := {([1], 9)}) rfl ⟨rfl, rfl, rfl⟩
      (by simp [resolve, pol0, ρid])) (.cons (.ret (w := []) (h := 5) (A := {([], 5)}) rfl
        ⟨rfl, rfl, rfl⟩ (by simp [resolve, pol0, ρid])) (.nil _))), by simp⟩⟩

end Silmaril.Accept.Parse.Examples
