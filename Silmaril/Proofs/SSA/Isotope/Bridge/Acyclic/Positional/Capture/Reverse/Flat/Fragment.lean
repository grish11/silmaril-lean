module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open Positional
open SSA.FiniteSum (append)
open Positional.Capture.Reverse (CheckedTable)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits n m : Nat} {β : BoundCtx τ n} {γ : BoundCtx τ m}
  {R : Fin blocks → τ} {D : Fin exits → τ}

/-! ## The target of a label -/

omit [TypeFormers τ] in
theorem target_locals_cast {L : LCtx τ} {A B : τ} (h : A = B) (t : Positional.Capture.Target R L A) :
    (cast (congrArg (Positional.Capture.Target R L) h) t).locals = t.locals := by
  subst h
  rfl

omit [TypeFormers τ] in
theorem target_index_cast {L : LCtx τ} {A B : τ} (h : A = B) (t : Positional.Capture.Target R L A) :
    (cast (congrArg (Positional.Capture.Target R L) h) t).index = t.index := by
  subst h
  rfl

omit [TypeFormers τ] in
/-- The local targets of the target of a label are the block of the label,
or none for an exit. -/
theorem labelTarget_locals_proof (i : Fin (blocks + exits)) :
    (labelTarget R D i).locals = Fin.addCases (fun j => [j]) (fun _ => []) i := by
  refine Fin.addCases (fun j => ?_) (fun e => ?_) i
  · simp only [labelTarget, Fin.addCases_left]
    exact target_locals_cast (SSA.FiniteSum.append_left R D j).symm (.local j)
  · simp only [labelTarget, Fin.addCases_right]
    rfl

omit [TypeFormers τ] in
/-- The target of a label has the index of the label. -/
theorem labelTarget_flatIndex_proof (i : Fin (blocks + exits)) :
    (labelTarget R D i).flatIndex List.length_ofFn = i := by
  refine Fin.addCases (fun j => ?_) (fun e => ?_) i
  · apply Fin.ext
    simp only [Positional.Capture.Target.flatIndex, labelTarget, Fin.addCases_left]
    exact target_index_cast (SSA.FiniteSum.append_left R D j).symm (.local j)
  · apply Fin.ext
    simp only [Positional.Capture.Target.flatIndex, labelTarget, Fin.addCases_right]
    rfl

/-! ## Lines, forks and rows -/

/-- A line jumps to its label only. -/
theorem line_jumps_proof : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ (blocks + exits) m} →
    (b : Body Φ (append R D) γ t) → ∀ r, b.line = some r → jumps t = [r.1]
  | _, _, _, .br i a, r, h => by
    cases h
    rfl
  | _, _, _, .let₁ a tail, r, h => by
    simp only [Body.line, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact line_jumps_proof tail r' hr'
  | _, _, _, .let₂ a tail, r, h => by
    simp only [Body.line, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact line_jumps_proof tail r' hr'
  | _, _, _, .case _ _ _, r, h => by
    simp [Body.line] at h

/-- A fork jumps to its two labels, in order. -/
theorem fork_jumps_proof : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ (blocks + exits) m} →
    (b : Body Φ (append R D) γ t) → ∀ r, b.fork = some r → jumps t = [r.1, r.2.1]
  | _, _, _, .br _ _, r, h => by
    simp [Body.fork] at h
  | _, _, _, .let₁ a tail, r, h => by
    simp only [Body.fork, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact fork_jumps_proof tail r' hr'
  | _, _, _, .let₂ a tail, r, h => by
    simp only [Body.fork, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact fork_jumps_proof tail r' hr'
  | _, _, _, .case e left right, r, h => by
    simp only [Body.fork, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, r', hr', rfl⟩ := h
    simp only [jumps, line_jumps_proof left l hl, line_jumps_proof right r' hr']
    rfl

omit [TypeFormers τ] in
/-- The local targets of a flat region are the blocks among its jumps. -/
theorem targets_jumps_proof : {m : Nat} → (t : Flat Φ (blocks + exits) m) →
    targets t = (jumps t).flatMap (fun i => Fin.addCases (fun j => [j]) (fun _ => []) i)
  | _, .br i _ => by simp [targets, jumps]
  | _, .let₁ _ tail => targets_jumps_proof tail
  | _, .let₂ _ tail => targets_jumps_proof tail
  | _, .case _ left right => by
    simp only [targets, jumps, List.flatMap_append, targets_jumps_proof left, targets_jumps_proof right]

/-- The row of a flat block jumps to the labels of the block, in order:
its flat image has the same jumps. -/
theorem row_jumps_proof {P : τ} {t : Flat Φ (blocks + exits) (n + 1)}
    (b : Body Φ (append R D) (β.snoc P) t) (row : Positional.Capture.Block Φ β R (List.ofFn D) P)
    (h : b.row = some row) : jumps (row.toFlat List.length_ofFn) = jumps t := by
  unfold Body.row at h
  cases hl : b.line with
  | some r =>
    rw [hl] at h
    cases h
    simp only [Positional.Capture.Block.toFlat, jumps, labelTarget_flatIndex_proof, line_jumps_proof b r hl]
  | none =>
    rw [hl] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    simp only [Positional.Capture.Block.toFlat, jumps, labelTarget_flatIndex_proof, fork_jumps_proof b r hr]
    rfl

/-- The row of a flat block has the local targets of the block. -/
theorem row_locals_proof {P : τ} {t : Flat Φ (blocks + exits) (n + 1)}
    (b : Body Φ (append R D) (β.snoc P) t) (row : Positional.Capture.Block Φ β R (List.ofFn D) P)
    (h : b.row = some row) : row.locals = targets t := by
  unfold Body.row at h
  cases hl : b.line with
  | some r =>
    rw [hl] at h
    cases h
    simp only [Positional.Capture.Block.locals, labelTarget_locals_proof, targets_jumps_proof t,
      line_jumps_proof b r hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | none =>
    rw [hl] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    simp only [Positional.Capture.Block.locals, labelTarget_locals_proof, targets_jumps_proof t,
      fork_jumps_proof b r hr, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ## The table -/

variable {size : Nat} {R : Fin (size + 1) → τ} {g : FiniteCFG Φ (size + 1) exits n}

/-- The table has the local targets of the flat graph, row by row. -/
theorem table_localTargets_proof (w : Witness g β R D) (h : w.Delimited) (i : Fin (size + 1)) :
    (w.table h).localTargets i = localTargets g i :=
  row_locals_proof (w.block i) _ (Option.some_get (h.rows i)).symm

/-- The rank check of the flat graph is the check of the table. -/
theorem table_check_proof (w : Witness g β R D) (h : w.Delimited)
    (ranked : Rank.check (localTargets g) = true) : (w.table h).check = true := by
  have same : (w.table h).localTargets = localTargets g := funext (table_localTargets_proof w h)
  unfold Positional.Capture.Table.check
  rw [same]
  exact ranked

/-- Every row of the table jumps to the labels of its flat block, in
order. -/
theorem table_jumps_proof (w : Witness g β R D) (h : w.Delimited) (i : Fin (size + 1)) :
    jumps (((w.table h).block i).toFlat List.length_ofFn) = jumps (g.block i) :=
  row_jumps_proof (w.block i) _ (Option.some_get (h.rows i)).symm

/-- The entry of a flat graph in the fragment jumps to the first block
only. -/
theorem entry_jumps_proof (w : Witness g β R D) (h : w.Delimited) :
    jumps g.entry = [Fin.castAdd exits 0] := by
  have he := h.entry
  unfold Witness.entryOperand at he
  cases hl : w.entry.line with
  | none =>
    rw [hl] at he
    simp at he
  | some r =>
    rw [hl] at he
    by_cases hr : r.1 = Fin.castAdd exits 0
    · rw [line_jumps_proof w.entry r hl, hr]
    · simp [hr] at he

/-! ## The shape of the fragment -/

section Shape

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {labels : Nat}
  {L : Fin labels → τ}

/-- The label of the line of a witnessed body is the label of the flat
body. -/
theorem line_label_proof : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ labels m} →
    (b : Body Φ L γ t) → b.line.map (·.1) = lineLabel t
  | _, _, _, .br _ _ => rfl
  | _, _, _, .let₁ _ tail => by
    simp only [Body.line, lineLabel, Option.map_map, ← line_label_proof tail]
    rfl
  | _, _, _, .let₂ _ tail => by
    simp only [Body.line, lineLabel, Option.map_map, ← line_label_proof tail]
    rfl
  | _, _, _, .case _ _ _ => rfl

/-- A witnessed body is a fork exactly when the flat body has the shape of
one. -/
theorem fork_shape_proof : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ labels m} →
    (b : Body Φ L γ t) → b.fork.isSome = forkShape t
  | _, _, _, .br _ _ => rfl
  | _, _, _, .let₁ _ tail => by
    simp only [Body.fork, forkShape, Option.isSome_map, fork_shape_proof tail]
  | _, _, _, .let₂ _ tail => by
    simp only [Body.fork, forkShape, Option.isSome_map, fork_shape_proof tail]
  | _, _, _, .case _ left right => by
    simp only [Body.fork, forkShape, ← line_label_proof left, ← line_label_proof right,
      Option.isSome_map]
    cases left.line <;> cases right.line <;> rfl

end Shape

section ShapeTable

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {size exits n : Nat}
  {β : BoundCtx τ n} {R : Fin (size + 1) → τ} {D : Fin exits → τ}
  {g : FiniteCFG Φ (size + 1) exits n}

/-- A witness of a flat graph of the shape of the fragment is in the
fragment. -/
theorem delimited_of_shape_proof (w : Witness g β R D) (shape : delimitedShape g = true) :
    w.Delimited := by
  simp only [delimitedShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at shape
  refine ⟨fun i => ?_, ?_⟩
  · have here := shape.2 i (List.mem_finRange i)
    have label := line_label_proof (w.block i)
    have fork := fork_shape_proof (w.block i)
    unfold Body.row
    cases found : (w.block i).line with
    | some r => rfl
    | none =>
      rw [found] at label
      have absent : lineLabel (g.block i) = none := label.symm
      simp only [absent, Option.isSome_none, Bool.false_eq_true, false_or] at here
      simp only [Option.isSome_map, fork, here]
  · have label := line_label_proof w.entry
    rw [shape.1] at label
    unfold Witness.entryOperand
    cases found : w.entry.line with
    | none => simp [found] at label
    | some r =>
      rw [found] at label
      have first : r.1 = Fin.castAdd exits 0 := Option.some.inj label
      simp only [Option.bind_some, first, dite_true, Option.isSome_some]

end ShapeTable

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
