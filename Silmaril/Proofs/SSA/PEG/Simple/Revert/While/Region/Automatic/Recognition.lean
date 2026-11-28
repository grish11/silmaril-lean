module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Thms
import Mathlib.Data.List.FinRange

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Proofs

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}

private theorem readRef [DecidableEq Data] (r : Ref g.sort t) :
    Ref.check g.sort t r.id.val = some r := by
  rcases r with ⟨i, typed⟩
  simp [Ref.check, i.isLt, typed]

private def expected (d : Descriptor g) (p : Port carried t) : CarriedRow g t :=
  ⟨d.theta.get p, d.initial.get p, d.next.get p⟩

private theorem readCandidate [DecidableEq Data] {d : Descriptor g} (b : Boundary g d)
    (p : Port carried t) : candidate g p (d.theta.get p).id = some (expected d p) := by
  unfold candidate
  rw [readRef (d.theta.get p)]
  dsimp only
  rw [b.thetaRow _ p]
  change (match nodeAt g (d.initial.get p) with
    | ⟨_, .param q, _⟩ =>
      letI := While.Check.portEq q p
      if q = p then some (expected d p) else none
    | _ => none) = _
  rw [b.initialRow _ p]
  simp [Node.ofLabel]

private theorem filterMap_singleton {α β : Type u} {f : α → Option β} {rows : List α}
    (distinct : rows.Nodup) {i : α} (present : i ∈ rows) {row : β}
    (found : f i = some row) (other : ∀ j, j ≠ i → f j = none) :
    rows.filterMap f = [row] := by
  induction rows with
  | nil => cases present
  | cons head tail ih =>
    obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp present with rfl | present
    · simp only [List.filterMap_cons_some found]
      rw [List.filterMap_eq_nil_iff.mpr (fun j hj => other j (fun eq => fresh (eq ▸ hj)))]
    · rw [List.filterMap_cons_none (other head (fun eq => fresh (eq ▸ present)))]
      exact ih tailDistinct present

private theorem collectRows [DecidableEq Data] {d : Descriptor g} (b : Boundary g d)
    (unique : ∀ t (p : Port carried t) i, i ≠ (d.theta.get p).id → candidate g p i = none)
    (ps : Tuple (Port carried) vars) :
    readCarried g ps = some (ps.map fun _ p => expected d p) := by
  induction ps with
  | nil => rfl
  | cons p tail ih =>
    have only := filterMap_singleton (rows := List.finRange n) (List.nodup_finRange n)
      (List.mem_finRange (d.theta.get p).id) (readCandidate b p) (unique _ p)
    simp [readCarried, candidates, only, ih, Tuple.map]

private theorem tuple_ext {F : Ty Data → Type w} (a b : Tuple F vars)
    (same : ∀ t (p : Port vars t), a.get p = b.get p) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons head tail ih =>
    cases b with
    | cons head' tail' =>
      have atHead : head = head' := same _ .head
      have atTail : tail = tail' := ih tail' (fun t p => same t (.tail p))
      rw [atHead, atTail]

theorem boundary_eq [DecidableEq Data] (d : Descriptor g) (b : Boundary g d)
    (count : thetaCount g = carried.length)
    (unique : ∀ t (p : Port carried t) i, i ≠ (d.theta.get p).id → candidate g p i = none) :
    inferBoundary g = some d := by
  let rows := (ports carried).map fun _ p => expected d p
  have theta : rows.map (fun _ row => row.theta) = d.theta := by
    apply tuple_ext
    intro t p
    simp only [rows, get_map, ports_get, expected]
  have initial : rows.map (fun _ row => row.initial) = d.initial := by
    apply tuple_ext
    intro t p
    simp only [rows, get_map, ports_get, expected]
  have step : rows.map (fun _ row => row.next) = d.next := by
    apply tuple_ext
    intro t p
    simp only [rows, get_map, ports_get, expected]
  have selected : readCarried g (ports carried) = some rows := collectRows b unique _
  have feedback (t : Ty Data) (p : Port carried t) :
      nodeAt g (d.theta.get p) =
        .ofLabel (.theta 0) (.cons (d.initial.get p) (.cons (d.next.get p) .nil)) :=
    b.thetaRow t p
  unfold inferBoundary
  simp only [b.evalRow, feedback, b.initialRow, b.passRow, b.negationRow, Node.ofLabel, Tuple.get,
    count, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, selected, theta, initial, step]
  cases d
  rfl

private theorem check_isSome_rank [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (d : Descriptor g) (guard body : List (Fin n)) {a b : DemandRank n 1}
    (validA : a.check g = true) (validB : b.check g = true) :
    (Region.check g d ⟨guard, body, a⟩).isSome = (Region.check g d ⟨guard, body, b⟩).isSome := by
  unfold Region.check Region.checkWith
  cases checkBoundary g d false <;> try rfl
  simp only [dite_eq_left validA, dite_eq_left validB]
  cases Schedule.check g d.guardRoots guard d.theta <;>
    cases Schedule.check g d.next body d.theta <;> rfl

theorem checkScheduled_isSome_rank [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (d : Descriptor g) {a b : DemandRank n 1}
    (validA : a.check g = true) (validB : b.check g = true) :
    (checkScheduled g d a).isSome = (checkScheduled g d b).isSome := by
  unfold checkScheduled checkScheduledWith
  cases sliceOrder g d d.guardRoots <;> cases sliceOrder g d d.next <;> try rfl
  exact check_isSome_rank d _ _ validA validB

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Proofs
