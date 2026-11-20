module

public import Silmaril.Semantics.Prolly.Cuts.Defs
public import Silmaril.Semantics.Prolly.Thms

public section

namespace Silmaril.Proofs.Semantics.Prolly.Cuts

open Silmaril.Semantics.Prolly

variable {Item Key Payload : Type}

private theorem noCuts_append {cut : Nat → Item → Bool} {left right : List Item} {count : Nat}
    (leftClean : NoCuts cut count left) (rightClean : NoCuts cut (count + left.length) right) :
    NoCuts cut count (left ++ right) := by
  induction left generalizing count with
  | nil => simpa using rightClean
  | cons head tail ih =>
    exact ⟨leftClean.1, ih leftClean.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightClean)⟩

private theorem partition_from {cut : Nat → Item → Bool} (items pending : List Item)
    (clean : NoCuts cut 0 pending) : CutPartition cut (chunkFrom cut pending items) := by
  induction items generalizing pending with
  | nil =>
    cases pending with
    | nil => exact .nil
    | cons head tail => exact .final (List.cons_ne_nil _ _) clean
  | cons head tail ih =>
    cases boundary : cut (pending.length + 1) head with
    | true => simpa [chunkFrom, boundary] using CutPartition.boundary clean boundary (ih [] trivial)
    | false =>
      have nextClean : NoCuts cut 0 (pending ++ [head]) :=
        noCuts_append clean ⟨by simpa using boundary, trivial⟩
      simpa [chunkFrom, boundary] using ih (pending ++ [head]) nextClean

private theorem skip_pending {cut : Nat → Item → Bool} (initial remaining pending : List Item)
    (clean : NoCuts cut pending.length initial) :
    chunkFrom cut pending (initial ++ remaining) = chunkFrom cut (pending ++ initial) remaining := by
  induction initial generalizing pending with
  | nil => simp
  | cons head tail ih =>
    have tailClean : NoCuts cut (pending ++ [head]).length tail := by simpa using clean.2
    simp [chunkFrom, clean.1, ih (pending ++ [head]) tailClean, List.append_assoc]

theorem partition_rebuild {cut : Nat → Item → Bool} {groups : List (List Item)}
    (valid : CutPartition cut groups) : chunk cut groups.flatten = groups := by
  induction valid with
  | nil => rfl
  | @final group nonempty clean =>
    have skipped := skip_pending (cut := cut) group [] [] clean
    simpa [chunk, chunkFrom, List.isEmpty_iff, nonempty] using skipped
  | @boundary initial last rest clean ends _ ih =>
    simp only [chunk, List.flatten_cons, List.append_assoc]
    rw [skip_pending initial ([last] ++ rest.flatten) [] clean]
    simpa [chunk, chunkFrom, ends] using congrArg ((initial ++ [last]) :: ·) ih

theorem partition_chunk (cut : Nat → Item → Bool) (items : List Item) : CutPartition cut (chunk cut items) :=
  partition_from items [] trivial

theorem grow_canonical_if_fits (policy : Policy Key) (fuel level : Nat) (node : Node Key Payload level)
    (fits : (grow policy fuel level node).root.length ≤ policy.width) :
    CanonicalGrowth policy level node (grow policy fuel level node) := by
  induction fuel generalizing level with
  | zero => exact .fits fits
  | succ fuel ih =>
    by_cases ready : node.length ≤ policy.width
    · simpa [grow, ready] using CanonicalGrowth.fits (policy := policy) ready
    · let cut (count : Nat) (pair : Key × Content Key Payload level) := policy.cut level count pair.1
      have step : grow policy (fuel + 1) level node = grow policy fuel (level + 1) (lift (chunk cut node)) := by
        simp only [grow, ite_eq_right ready, cut]
      rw [step] at fits ⊢
      exact .step (Nat.lt_of_not_ge ready) (flatten_chunk cut node) (partition_chunk cut node) (ih _ _ fits)

private theorem level_le_of_growth {policy : Policy Key} {level : Nat} {node : Node Key Payload level}
    {tree : Tree Key Payload} (canonical : CanonicalGrowth policy level node tree) : level ≤ tree.level := by
  induction canonical with
  | fits => exact Nat.le_refl _
  | step _ _ _ _ above => exact Nat.le_trans (Nat.le_succ _) above

theorem growth_executes {policy : Policy Key} {level : Nat} {node : Node Key Payload level}
    {tree : Tree Key Payload} (proof : CanonicalGrowth policy level node tree) {fuel : Nat}
    (enough : tree.level ≤ level + fuel) : grow policy fuel level node = tree := by
  induction proof generalizing fuel with
  | fits fit => cases fuel <;> simp [grow, fit]
  | @step level node groups tree wide whole valid next ih =>
    have isHigher := level_le_of_growth next
    cases fuel with
    | zero => omega
    | succ fuel =>
      have same : chunk (fun count pair => policy.cut level count pair.1) node = groups :=
        whole ▸ partition_rebuild valid
      simp only [grow, ite_eq_right (Nat.not_le_of_gt wide), same]
      exact ih (by omega)

private theorem root_fits {width : Nat} {tree : Tree Key Payload} (bounded : tree.Bounded width) :
    tree.root.length ≤ width := by
  obtain ⟨level, root⟩ := tree
  cases level with
  | zero => exact bounded
  | succ level => exact bounded.1

theorem build_canonical [LinearOrder Key] (policy : Policy Key) (map : Silmaril.Semantics.OrderedMap Key Payload) :
    CanonicalGrowth policy 0 map.entries (build policy map) :=
  grow_canonical_if_fits policy _ _ _ (root_fits (build_bounded policy map))

end Silmaril.Proofs.Semantics.Prolly.Cuts
