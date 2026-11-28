module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Defs

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL (Model Val Op upd)
open Silmaril.SSA.LambdaRTL.CFG (Body Term)

universe v w

variable {V W K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-! ## Reads under a renaming -/

/-- A renamed value reads the store through the renaming. -/
theorem eval_rename_proof (model : Model F M α) (read : V → W) (store : W → α) :
    (value : Val V) → (value.rename read).eval model store = value.eval model (store ∘ read)
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    simp only [Val.rename, Val.eval]
    rw [eval_rename_proof model read store a, eval_rename_proof model read store b]

/-- A renamed operand reads the store through the renaming. -/
theorem op_eval_rename_proof [Monad M] (model : Model F M α) (read : V → W) (store : W → α)
    (operand : Op V F) :
    (operand.rename read).eval model store = operand.eval model (store ∘ read) := by
  cases operand <;> simp only [Op.rename, Op.eval, eval_rename_proof]

/-! ## Stores of the normalized graph -/

section Stores

variable [DecidableEq V] [DecidableEq K]

/-- Writing an original register writes the original part of the store. -/
theorem upd_left_proof (store : Name V K → α) (x : V) (a : α) :
    upd store (.inl x) a ∘ Sum.inl = upd (store ∘ Sum.inl) x a := by
  funext y
  simp only [Function.comp, upd, Sum.inl.injEq]

/-- Writing an original register leaves the copies. -/
theorem upd_right_proof (store : Name V K → α) (x : V) (a : α) :
    upd store (.inl x) a ∘ Sum.inr = store ∘ Sum.inr := by
  funext c
  simp only [Function.comp, upd, reduceCtorEq, ite_false]

/-- Writing an original register keeps the copies of a reader in step
with the registers, when the reader reads the written register itself. -/
theorem synced_upd_proof (read : V → Name V K) (local_ : ∀ y z, read y = .inl z → z = y)
    (store : Name V K → α) (synced : ∀ y, store (read y) = store (.inl y)) (x : V) (a : α)
    (own : read x = .inl x) (y : V) :
    upd store (.inl x) a (read y) = upd store (.inl x) a (.inl y) := by
  by_cases same : y = x
  · subst same
    rw [own]
  · have other : read y ≠ .inl x := fun eq => same (local_ y x eq).symm
    simp only [upd, other, ite_false, Sum.inl.injEq, same, synced y]

/-- The reader of the entry or of a block renames a register to itself or
to a copy of itself. -/
theorem reader_local_proof (table : Table V K) (pred : Option K) (y z : V)
    (eq : reader table pred y = .inl z) : z = y := by
  cases pred with
  | none => exact (Sum.inl.inj eq).symm
  | some key =>
    simp only [reader] at eq
    split at eq
    · cases eq
    · exact (Sum.inl.inj eq).symm

end Stores

/-! ## Execution of a body -/

section Exec

variable [Monad M] [DecidableEq V] [DecidableEq K]

/-- A terminator of the normalized graph runs like the original
terminator on the original part of the store, and keeps the copies. -/
theorem exec_term_proof (model : Model F M α) {R : Type w} (read : V → Name V K)
    (local_ : ∀ y z, read y = .inl z → z = y) (next : Option K → α → (Name V K → α) → M R) :
    (tail : Term V (Option K) F) → (store : Name V K → α) →
    (∀ y, store (read y) = store (.inl y)) →
    (∀ x ∈ GlobalSSA.termDefinitions tail, read x = .inl x) →
    (term read tail).exec model next store =
      tail.exec model (fun k a s => next k a (Sum.elim s (store ∘ Sum.inr))) (store ∘ Sum.inl)
  | .br target value, store, synced, _ => by
    simp only [term, Term.exec, eval_rename_proof]
    rw [show store ∘ read = store ∘ Sum.inl from funext synced, Sum.elim_comp_inl_inr]
  | .case operand x left y right, store, synced, defs => by
    simp only [term, Term.exec, op_eval_rename_proof]
    rw [show store ∘ read = store ∘ Sum.inl from funext synced]
    congr 1
    funext choice
    cases choice with
    | inl a =>
      have own : read x = .inl x := defs x (by simp [GlobalSSA.termDefinitions])
      have step := exec_term_proof model read local_ next left (upd store (.inl x) a)
        (synced_upd_proof read local_ store synced x a own)
        (fun z hz => defs z (by simp [GlobalSSA.termDefinitions, hz]))
      rw [upd_left_proof, upd_right_proof] at step
      exact step
    | inr b =>
      have own : read y = .inl y := defs y (by simp [GlobalSSA.termDefinitions])
      have step := exec_term_proof model read local_ next right (upd store (.inl y) b)
        (synced_upd_proof read local_ store synced y b own)
        (fun z hz => defs z (by simp [GlobalSSA.termDefinitions, hz]))
      rw [upd_left_proof, upd_right_proof] at step
      exact step

/-- A body of the normalized graph runs like the original body on the
original part of the store, and keeps the copies. -/
theorem exec_body_proof (model : Model F M α) {R : Type w} (read : V → Name V K)
    (local_ : ∀ y z, read y = .inl z → z = y) (next : Option K → α → (Name V K → α) → M R) :
    (source : Body V (Option K) F) → (store : Name V K → α) →
    (∀ y, store (read y) = store (.inl y)) →
    (∀ x ∈ GlobalSSA.bodyDefinitions source, read x = .inl x) →
    (body read source).exec model next store =
      source.exec model (fun k a s => next k a (Sum.elim s (store ∘ Sum.inr))) (store ∘ Sum.inl)
  | .term tail, store, synced, defs => exec_term_proof model read local_ next tail store synced defs
  | .let1 x operand rest, store, synced, defs => by
    simp only [body, Body.exec, op_eval_rename_proof]
    rw [show store ∘ read = store ∘ Sum.inl from funext synced]
    congr 1
    funext a
    have own : read x = .inl x := defs x (by simp [GlobalSSA.bodyDefinitions])
    have step := exec_body_proof model read local_ next rest (upd store (.inl x) a)
      (synced_upd_proof read local_ store synced x a own)
      (fun z hz => defs z (by simp [GlobalSSA.bodyDefinitions, hz]))
    rw [upd_left_proof, upd_right_proof] at step
    exact step
  | .let2 x y operand rest, store, synced, defs => by
    simp only [body, Body.exec, op_eval_rename_proof]
    rw [show store ∘ read = store ∘ Sum.inl from funext synced]
    congr 1
    funext p
    have ownX : read x = .inl x := defs x (by simp [GlobalSSA.bodyDefinitions])
    have ownY : read y = .inl y := defs y (by simp [GlobalSSA.bodyDefinitions])
    have step := exec_body_proof model read local_ next rest
      (upd (upd store (.inl x) p.1) (.inl y) p.2)
      (synced_upd_proof read local_ _ (synced_upd_proof read local_ store synced x p.1 ownX) y p.2
        ownY)
      (fun z hz => defs z (by simp [GlobalSSA.bodyDefinitions, hz]))
    rw [upd_left_proof, upd_right_proof, upd_left_proof, upd_right_proof] at step
    exact step

omit [DecidableEq K] in
/-- Two continuations give the same run of a terminator when they agree
at its targets, on the stores that differ from the starting store at its
definitions only. -/
theorem term_congr_proof (model : Model F M α) {R : Type w}
    (next next' : Option K → α → (V → α) → M R) :
    (tail : Term V (Option K) F) → (store : V → α) →
    (∀ k a s, k ∈ tail.targets → (∀ x, x ∉ GlobalSSA.termDefinitions tail → s x = store x) →
      next k a s = next' k a s) →
    tail.exec model next store = tail.exec model next' store
  | .br target value, store, same =>
    same _ _ _ (by simp [Term.targets]) (fun _ _ => rfl)
  | .case operand x left y right, store, same => by
    simp only [Term.exec]
    congr 1
    funext choice
    cases choice with
    | inl a =>
      exact term_congr_proof model next next' left (upd store x a) fun k a' s member frame =>
        same k a' s (by simp [Term.targets, member]) fun z hz => by
          simp only [GlobalSSA.termDefinitions, List.mem_append, List.mem_cons, not_or] at hz
          rw [frame z hz.1.2]
          simp only [upd, hz.1.1, ite_false]
    | inr b =>
      exact term_congr_proof model next next' right (upd store y b) fun k a' s member frame =>
        same k a' s (by simp [Term.targets, member]) fun z hz => by
          simp only [GlobalSSA.termDefinitions, List.mem_append, List.mem_cons, not_or] at hz
          rw [frame z hz.2.2]
          simp only [upd, hz.2.1, ite_false]

omit [DecidableEq K] in
/-- Two continuations give the same run of a body when they agree at its
targets, on the stores that differ from the starting store at its
definitions only. -/
theorem body_congr_proof (model : Model F M α) {R : Type w}
    (next next' : Option K → α → (V → α) → M R) :
    (source : Body V (Option K) F) → (store : V → α) →
    (∀ k a s, k ∈ source.targets → (∀ x, x ∉ GlobalSSA.bodyDefinitions source → s x = store x) →
      next k a s = next' k a s) →
    source.exec model next store = source.exec model next' store
  | .term tail, store, same => term_congr_proof model next next' tail store same
  | .let1 x operand rest, store, same => by
    simp only [Body.exec]
    congr 1
    funext a
    exact body_congr_proof model next next' rest (upd store x a) fun k a' s member frame =>
      same k a' s member fun z hz => by
        simp only [GlobalSSA.bodyDefinitions, List.mem_cons, not_or] at hz
        rw [frame z hz.2]
        simp only [upd, hz.1, ite_false]
  | .let2 x y operand rest, store, same => by
    simp only [Body.exec]
    congr 1
    funext p
    exact body_congr_proof model next next' rest (upd (upd store x p.1) y p.2)
      fun k a' s member frame => same k a' s member fun z hz => by
        simp only [GlobalSSA.bodyDefinitions, List.mem_cons, not_or] at hz
        rw [frame z hz.2.2]
        simp only [upd, hz.1, hz.2.1, ite_false]

omit [DecidableEq K] in
/-- A computation after a terminator runs in its continuation. -/
theorem term_bind_proof [LawfulMonad M] (model : Model F M α) {R S : Type w}
    (next : Option K → α → (V → α) → M R) (after : R → M S) :
    (tail : Term V (Option K) F) → (store : V → α) →
    tail.exec model next store >>= after =
      tail.exec model (fun k a s => next k a s >>= after) store
  | .br _ _, _ => rfl
  | .case operand x left y right, store => by
    simp only [Term.exec, bind_assoc]
    congr 1
    funext value
    congr 1
    funext choice
    cases choice with
    | inl a => exact term_bind_proof model next after left _
    | inr b => exact term_bind_proof model next after right _

omit [DecidableEq K] in
/-- A computation after a body runs in its continuation. -/
theorem body_bind_proof [LawfulMonad M] (model : Model F M α) {R S : Type w}
    (next : Option K → α → (V → α) → M R) (after : R → M S) :
    (source : Body V (Option K) F) → (store : V → α) →
    source.exec model next store >>= after =
      source.exec model (fun k a s => next k a s >>= after) store
  | .term tail, store => term_bind_proof model next after tail store
  | .let1 x operand rest, store => by
    simp only [Body.exec, bind_assoc]
    congr 1
    funext a
    exact body_bind_proof model next after rest _
  | .let2 x y operand rest, store => by
    simp only [Body.exec, bind_assoc]
    congr 1
    funext value
    congr 1
    funext p
    exact body_bind_proof model next after rest _

end Exec

/-! ## Lookup -/

section Lookup

variable [DecidableEq K]

/-- A found entry of an association list is a member of the list. -/
theorem lookup_mem_proof {B : Type*} : (entries : List (K × B)) → {key : K} → {value : B} →
    entries.lookup key = some value → (key, value) ∈ entries
  | [], _, _, found => by cases found
  | (k, b) :: rest, key, value, found => by
    simp only [List.lookup] at found
    split at found
    · rename_i same
      cases found
      rw [eq_of_beq same]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem_proof rest found)

/-- Looking up a key in a list whose values were mapped by a function of
the key. -/
theorem lookup_keyed_proof {B C : Type*} (f : K → B → C) : (entries : List (K × B)) → (key : K) →
    (entries.map fun (k, b) => (k, f k b)).lookup key = (entries.lookup key).map (f key)
  | [], _ => rfl
  | (k, b) :: rest, key => by
    simp only [List.map, List.lookup]
    split
    · rename_i same
      rw [eq_of_beq same]
      rfl
    · exact lookup_keyed_proof f rest key

/-- The normalized graph has a block exactly where the original graph has
one, and it is the normalized block. -/
theorem lookup_forward_proof [DecidableEq V] (graph : Graph V K F) (table : Table V K) (key : K) :
    (forward graph table).blocks.lookup key =
      (graph.blocks.lookup key).map (block table graph key) :=
  lookup_keyed_proof (block table graph) graph.blocks key

/-- The body of the entry or of a block. -/
def bodyAt (graph : Graph V K F) : Option K → Option (Body V (Option K) F)
  | none => some graph.entry
  | some key => (graph.blocks.lookup key).map Block.body

/-- The entry or a block that jumps to a block is one of its listed
predecessors. -/
theorem mem_predecessors_proof (graph : Graph V K F) (pred : Option K) (key : K)
    {source : Body V (Option K) F} (at_ : bodyAt graph pred = some source)
    (edge : some key ∈ source.targets) : pred ∈ graph.predecessors key := by
  cases pred with
  | none =>
    cases at_
    simp [Graph.predecessors, edge]
  | some label =>
    simp only [bodyAt, Option.map_eq_some_iff] at at_
    obtain ⟨found, at_, rfl⟩ := at_
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨(label, found), lookup_mem_proof _ at_, ?_⟩)
    simp [edge]

/-- A checked table lists no register that its block defines. -/
theorem check_block_proof [DecidableEq V] (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) {key : K} {source : Block V K F}
    (found : graph.blocks.lookup key = some source) {register : V}
    (received : register ∈ table.received key) :
    register ∉ source.rows.map Row.dst ∧ register ∉ GlobalSSA.bodyDefinitions source.body := by
  simp only [check, List.all_eq_true] at ok
  have := ok (key, source) (lookup_mem_proof _ found) register received
  simpa [not_or] using this

end Lookup

/-! ## Targets and exits -/

section Exits

/-- A normalized terminator has the targets of the original. -/
theorem term_targets_proof (read : V → Name V K) :
    (tail : Term V (Option K) F) → (term read tail).targets = tail.targets
  | .br _ _ => rfl
  | .case _ _ left _ right => by
    simp only [term, Term.targets, term_targets_proof read left, term_targets_proof read right]

/-- A normalized body has the targets of the original. -/
theorem body_targets_proof (read : V → Name V K) :
    (source : Body V (Option K) F) → (body read source).targets = source.targets
  | .term tail => term_targets_proof read tail
  | .let1 _ _ rest => body_targets_proof read rest
  | .let2 _ _ _ rest => body_targets_proof read rest

variable [DecidableEq V] [DecidableEq K]

/-- A label is a block of the normalized graph exactly when it is a block
of the original graph. -/
theorem lookup_isSome_proof (graph : Graph V K F) (table : Table V K) (target : Option K) :
    (OrderedExits.lookup (forward graph table) target).isSome =
      (OrderedExits.lookup graph target).isSome := by
  cases target with
  | none => rfl
  | some key =>
    simp only [OrderedExits.lookup, Option.bind_some]
    rw [lookup_forward_proof]
    cases graph.blocks.lookup key <;> rfl

/-- The normalized graph has the exit partition of the original graph. -/
theorem checkExits_forward_proof (graph : Graph V K F) (table : Table V K)
    (exits : List (Option K)) :
    OrderedExits.checkExits (forward graph table) exits = OrderedExits.checkExits graph exits := by
  have targets : (forward graph table).entry.targets ++
      (forward graph table).blocks.flatMap (fun item => item.2.body.targets) =
      graph.entry.targets ++ graph.blocks.flatMap (fun item => item.2.body.targets) := by
    simp only [forward, List.flatMap_map, block, body_targets_proof]
  have none : ∀ target, (OrderedExits.lookup (forward graph table) target).isNone =
      (OrderedExits.lookup graph target).isNone := fun target => by
    have some := lookup_isSome_proof graph table target
    cases looked : OrderedExits.lookup graph target <;>
      cases forwarded : OrderedExits.lookup (forward graph table) target <;>
      simp_all
  simp only [OrderedExits.checkExits, targets, none, lookup_isSome_proof]

end Exits

/-! ## The φ assignment -/

section Assign

variable [DecidableEq V] [DecidableEq K]

/-- The operand of an original row for a predecessor is the original
operand, read as the predecessor reads it. -/
theorem lookup_row_proof (table : Table V K) (source : Option K) :
    (incoming : List (Option K × Val V)) →
    (incoming.map fun (pred, value) => (pred, value.rename (reader table pred))).lookup source =
      (incoming.lookup source).map (·.rename (reader table source))
  | [] => rfl
  | (pred, value) :: rest => by
    simp only [List.map, List.lookup]
    split
    · rename_i same
      rw [eq_of_beq same]
      rfl
    · exact lookup_row_proof table source rest

theorem operand_row_proof (table : Table V K) (source : Option K) (r : Row V K) :
    (row table r).operand source = (r.operand source).rename (reader table source) := by
  simp only [Row.operand, row, lookup_row_proof]
  cases r.incoming.lookup source <;> rfl

/-- The operand of a copy row for a listed predecessor is the register as
the predecessor reads it. -/
theorem lookup_copy_proof (table : Table V K) (register : V) (source : Option K) :
    (predecessors : List (Option K)) → source ∈ predecessors →
    (predecessors.map fun pred => (pred, Val.var (reader table pred register))).lookup source =
      some (.var (reader table source register))
  | [], member => by cases member
  | pred :: rest, member => by
    simp only [List.map, List.lookup]
    split
    · rename_i same
      rw [eq_of_beq same]
    · rename_i other
      have differs : source ≠ pred := fun eq => by simp [eq] at other
      exact lookup_copy_proof table register source rest
        ((List.mem_cons.mp member).resolve_left differs)

omit [DecidableEq V] in
/-- Assigning two lists of rows in order. -/
theorem assign_append_proof {W : Type w} [DecidableEq W] (model : Model F M α) (source : Option K)
    (snapshot : W → α) : (first second : List (Row W K)) → (store : W → α) →
    assign model source snapshot (first ++ second) store =
      assign model source snapshot second (assign model source snapshot first store)
  | [], _, _ => rfl
  | _ :: rest, second, _ => assign_append_proof model source snapshot rest second _

omit [DecidableEq V] in
/-- An assignment changes its destinations only. -/
theorem assign_other_proof {W : Type w} [DecidableEq W] (model : Model F M α) (source : Option K)
    (snapshot : W → α) : (rows : List (Row W K)) → (store : W → α) → (x : W) →
    x ∉ rows.map Row.dst → assign model source snapshot rows store x = store x
  | [], _, _, _ => rfl
  | r :: rest, store, x, other => by
    simp only [List.map, List.mem_cons, not_or] at other
    rw [assign, assign_other_proof model source snapshot rest _ x other.2]
    simp only [upd, other.1, ite_false]

/-- The original rows of the normalized graph assign the original
registers as in the original graph, and leave the copies. -/
theorem assign_rows_proof (model : Model F M α) (table : Table V K) (source : Option K)
    (snapshot : Name V K → α)
    (synced : ∀ y, snapshot (reader table source y) = snapshot (.inl y)) :
    (rows : List (Row V K)) → (store : Name V K → α) →
    assign model source snapshot (rows.map (row table)) store =
      Sum.elim (assign model source (snapshot ∘ Sum.inl) rows (store ∘ Sum.inl)) (store ∘ Sum.inr)
  | [], store => (Sum.elim_comp_inl_inr store).symm
  | r :: rest, store => by
    simp only [List.map, assign]
    rw [assign_rows_proof model table source snapshot synced rest, operand_row_proof,
      eval_rename_proof, show snapshot ∘ reader table source = snapshot ∘ Sum.inl from funext synced]
    show Sum.elim (assign model source (snapshot ∘ Sum.inl) rest
      (upd store (.inl r.dst) _ ∘ Sum.inl)) (upd store (.inl r.dst) _ ∘ Sum.inr) = _
    rw [upd_left_proof, upd_right_proof]

/-- The copy rows leave the original registers, and give each listed
register its value in the store of the predecessor. -/
theorem assign_copies_proof (model : Model F M α) (table : Table V K) (source : Option K)
    (snapshot : Name V K → α)
    (synced : ∀ y, snapshot (reader table source y) = snapshot (.inl y))
    (predecessors : List (Option K)) (member : source ∈ predecessors) (key : K) :
    (registers : List V) → (store : Name V K → α) →
    assign model source snapshot (registers.map (copyRow table predecessors key)) store ∘ Sum.inl =
        store ∘ Sum.inl ∧
      ∀ r, r ∈ registers ∨ store (.inr (r, key)) = snapshot (.inl r) →
        assign model source snapshot (registers.map (copyRow table predecessors key)) store
          (.inr (r, key)) = snapshot (.inl r)
  | [], store => ⟨rfl, fun r h => h.resolve_left (by simp)⟩
  | first :: rest, store => by
    have value : ((copyRow table predecessors key first).operand source).eval model snapshot =
        snapshot (.inl first) := by
      simp only [Row.operand, copyRow, lookup_copy_proof table first source predecessors member,
        Option.getD_some, Val.eval, synced]
    have step := assign_copies_proof model table source snapshot synced predecessors member key rest
      (upd store (.inr (first, key)) (snapshot (.inl first)))
    simp only [List.map, assign, value]
    refine ⟨step.1.trans ?_, fun r h => step.2 r ?_⟩
    · funext y
      simp only [Function.comp, upd, reduceCtorEq, ite_false]
    · by_cases same : r = first
      · subst same
        exact .inr (by simp [upd])
      · rcases h with h | h
        · exact .inl ((List.mem_cons.mp h).resolve_left same)
        · exact .inr (by simp [upd, same, h])

end Assign

/-! ## One step

A pending transfer of the normalized graph is kept when it comes from a
jump that is written in the original graph and the copies of its source
are in step with the registers. A kept transfer steps like its original
part, to a kept transfer. -/

section Step

variable [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq K]

/-- The invariant of the pending transfers of the normalized graph. -/
def Kept (graph : Graph V K F) (table : Table V K)
    (pending : OrderedExits.Pending (Name V K) K α) : Prop :=
  (∃ source, bodyAt graph pending.1 = some source ∧ pending.2.1 ∈ source.targets) ∧
    ∀ y, pending.2.2.2 (reader table pending.1 y) = pending.2.2.2 (.inl y)

/-- The original part of a pending transfer. -/
def project (pending : OrderedExits.Pending (Name V K) K α) : OrderedExits.Pending V K α :=
  (pending.1, pending.2.1, pending.2.2.1, pending.2.2.2 ∘ Sum.inl)

omit [LawfulMonad M] in
/-- At a label that is not a block, the normalized graph returns. -/
theorem step_exit_proof (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (pred target : Option K) (value : α) (store : Name V K → α)
    (miss : OrderedExits.lookup graph target = none) :
    OrderedExits.step model (forward graph table) (pred, target, value, store) =
      pure (.inl (target, value)) := by
  have missed : OrderedExits.lookup (forward graph table) target = none := by
    cases target with
    | none => rfl
    | some key =>
      simp only [OrderedExits.lookup, Option.bind_some] at miss ⊢
      rw [lookup_forward_proof, miss]
      rfl
  simp only [OrderedExits.step, missed]

omit [LawfulMonad M] in
/-- A step of the original graph into a block. -/
theorem step_source_proof (model : Model F M α) (graph : Graph V K F) (pred : Option K) (key : K)
    (value : α) (store : V → α) {source : Block V K F}
    (found : graph.blocks.lookup key = some source) :
    OrderedExits.step model graph (pred, some key, value, store) =
      Sum.inr <$> source.body.exec model (fun k a s => pure (some key, k, a, s))
        (assign model pred store source.rows store) := by
  simp only [OrderedExits.step, OrderedExits.lookup, Option.bind_some, found, OrderedExits.execute]

omit [Monad M] [LawfulMonad M] in
/-- The store of a kept transfer after the φ rows of the normalized
block: its original part is the store after the original rows, and each
received register has its copy in step. -/
theorem assigned_proof (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) (pred : Option K) (key : K) (value : α)
    (store : Name V K → α) {source : Block V K F} (found : graph.blocks.lookup key = some source)
    (kept : Kept graph table (pred, some key, value, store)) :
    assign model pred store (block table graph key source).rows store ∘ Sum.inl =
        assign model pred (store ∘ Sum.inl) source.rows (store ∘ Sum.inl) ∧
      ∀ r ∈ table.received key,
        assign model pred store (block table graph key source).rows store (.inr (r, key)) =
          assign model pred (store ∘ Sum.inl) source.rows (store ∘ Sum.inl) r := by
  obtain ⟨⟨from_, at_, edge⟩, synced⟩ := kept
  have member := mem_predecessors_proof graph pred key at_ edge
  have rows := assign_rows_proof model table pred store synced source.rows store
  have copies := assign_copies_proof model table pred store synced (graph.predecessors key) member key
    (table.received key) (assign model pred store (source.rows.map (row table)) store)
  have whole : assign model pred store (block table graph key source).rows store =
      assign model pred store ((table.received key).map (copyRow table (graph.predecessors key) key))
        (assign model pred store (source.rows.map (row table)) store) :=
    assign_append_proof model pred store _ _ store
  have left : assign model pred store (block table graph key source).rows store ∘ Sum.inl =
      assign model pred (store ∘ Sum.inl) source.rows (store ∘ Sum.inl) := by
    rw [whole, copies.1, rows]
    rfl
  refine ⟨left, fun r received => ?_⟩
  rw [whole, copies.2 r (.inl received)]
  exact (assign_other_proof model pred (store ∘ Sum.inl) source.rows (store ∘ Sum.inl) r
    (check_block_proof graph table ok found received).1).symm

omit [LawfulMonad M] in
/-- A step of the normalized graph from a kept transfer into a block runs
the original body from the store after the original rows. -/
theorem step_block_proof (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) (pred : Option K) (key : K) (value : α)
    (store : Name V K → α) {source : Block V K F} (found : graph.blocks.lookup key = some source)
    (kept : Kept graph table (pred, some key, value, store)) :
    OrderedExits.step model (forward graph table) (pred, some key, value, store) =
      Sum.inr <$> source.body.exec model
        (fun k a s => pure (some key, k, a, Sum.elim s
          (assign model pred store (block table graph key source).rows store ∘ Sum.inr)))
        (assign model pred (store ∘ Sum.inl) source.rows (store ∘ Sum.inl)) := by
  have looked : OrderedExits.lookup (forward graph table) (some key) =
      some (block table graph key source) := by
    simp only [OrderedExits.lookup, Option.bind_some]
    rw [lookup_forward_proof, found]
    rfl
  have assigned := assigned_proof model graph table ok pred key value store found kept
  have synced : ∀ y, assign model pred store (block table graph key source).rows store
      (reader table (some key) y) =
      assign model pred store (block table graph key source).rows store (.inl y) := fun y => by
    simp only [reader]
    split
    · rename_i received
      rw [assigned.2 y received]
      exact (congrFun assigned.1 y).symm
    · rfl
  have own : ∀ x ∈ GlobalSSA.bodyDefinitions source.body, reader table (some key) x = .inl x :=
    fun x defined => by
      have other : x ∉ table.received key := fun received =>
        (check_block_proof graph table ok found received).2 defined
      simp only [reader, other, ↓reduceIte]
  simp only [OrderedExits.step, looked, OrderedExits.execute]
  rw [show (block table graph key source).body = body (reader table (some key)) source.body from rfl,
    exec_body_proof model (reader table (some key)) (reader_local_proof table (some key)) _
      source.body _ synced own, assigned.1]

omit [Monad M] [LawfulMonad M] in
/-- The transfer that a kept transfer steps to is kept, at the targets of
the block and on the stores that the block can reach. -/
theorem kept_next_proof (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) (pred : Option K) (key : K) (value : α)
    (store : Name V K → α) {source : Block V K F} (found : graph.blocks.lookup key = some source)
    (kept : Kept graph table (pred, some key, value, store)) (target : Option K) (a : α)
    (s : V → α) (member : target ∈ source.body.targets)
    (frame : ∀ x, x ∉ GlobalSSA.bodyDefinitions source.body →
      s x = assign model pred (store ∘ Sum.inl) source.rows (store ∘ Sum.inl) x) :
    Kept graph table (some key, target, a, Sum.elim s
      (assign model pred store (block table graph key source).rows store ∘ Sum.inr)) := by
  have assigned := assigned_proof model graph table ok pred key value store found kept
  refine ⟨⟨source.body, by simp [bodyAt, found], member⟩, fun y => ?_⟩
  simp only [reader]
  split
  · rename_i received
    simp only [Sum.elim_inr, Sum.elim_inl, Function.comp]
    rw [assigned.2 y received, frame y (check_block_proof graph table ok found received).2]
  · rfl

end Step

/-! ## The run -/

section Run

variable [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M] [DecidableEq V] [DecidableEq K]

/-- From a kept transfer, the normalized graph iterates like the original
graph from its original part. -/
theorem iter_forward_proof (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) (pending : OrderedExits.Pending (Name V K) K α)
    (kept : Kept graph table pending) :
    iter (OrderedExits.step model (forward graph table)) pending =
      iter (OrderedExits.step model graph) (project pending) := by
  classical
  let keep (a : {p // Kept (α := α) graph table p}) (next : OrderedExits.Pending (Name V K) K α) :
      {p // Kept (α := α) graph table p} :=
    if good : Kept graph table next then ⟨next, good⟩ else a
  let stepKept : {p // Kept (α := α) graph table p} →
      M ((Option K × α) ⊕ {p // Kept (α := α) graph table p}) :=
    fun a => Sum.map id (keep a) <$> OrderedExits.step model (forward graph table) a.1
  have toNormalized : (stepKept >=> liftPure (Sum.map id Subtype.val)) =
      (liftPure Subtype.val >=> OrderedExits.step model (forward graph table)) := by
    funext a
    obtain ⟨⟨pred, target, value, store⟩, kept⟩ := a
    simp only [Bind.kleisliRight, liftPure, Function.comp, pure_bind, stepKept, map_eq_pure_bind,
      bind_assoc]
    cases looked : OrderedExits.lookup graph target with
    | none =>
      rw [step_exit_proof model graph table pred target value store looked]
      simp only [pure_bind, Sum.map_inl, id]
    | some source =>
      cases target with
      | none => cases looked
      | some key =>
        have found : graph.blocks.lookup key = some source := looked
        rw [step_block_proof model graph table ok pred key value store found kept]
        simp only [map_eq_pure_bind, body_bind_proof, pure_bind, Sum.map_inr]
        exact body_congr_proof model _ _ source.body _ fun k a s member frame => by
          have good := kept_next_proof model graph table ok pred key value store found kept k a s
            member frame
          simp only [keep, good, ↓reduceDIte]
  have toSource : (stepKept >=> liftPure (Sum.map id (project ∘ Subtype.val))) =
      (liftPure (project ∘ Subtype.val) >=> OrderedExits.step model graph) := by
    funext a
    obtain ⟨⟨pred, target, value, store⟩, kept⟩ := a
    simp only [Bind.kleisliRight, liftPure, Function.comp, pure_bind, stepKept, map_eq_pure_bind,
      bind_assoc]
    cases looked : OrderedExits.lookup graph target with
    | none =>
      rw [step_exit_proof model graph table pred target value store looked]
      simp only [pure_bind, Sum.map_inl, id, project, OrderedExits.step, looked]
    | some source =>
      cases target with
      | none => cases looked
      | some key =>
        have found : graph.blocks.lookup key = some source := looked
        rw [step_block_proof model graph table ok pred key value store found kept]
        simp only [project]
        rw [step_source_proof model graph pred key value (store ∘ Sum.inl) found]
        simp only [map_eq_pure_bind, body_bind_proof, pure_bind, Sum.map_inr]
        exact body_congr_proof model _ _ source.body _ fun k a s member frame => by
          have good := kept_next_proof model graph table ok pred key value store found kept k a s
            member frame
          simp only [keep, good, ↓reduceDIte]
          rfl
  have first := congrFun (LawfulElgotMonad.uniformity stepKept
    (OrderedExits.step model (forward graph table)) Subtype.val toNormalized) ⟨pending, kept⟩
  have second := congrFun (LawfulElgotMonad.uniformity stepKept (OrderedExits.step model graph)
    (project ∘ Subtype.val) toSource) ⟨pending, kept⟩
  simp only [Bind.kleisliRight, liftPure, Function.comp, pure_bind] at first second
  exact first.symm.trans second

/-- The normalized graph runs like the original graph on the original
part of its input, for any values of the copies. -/
theorem run_forward_proof (model : Model F M α) (graph : Graph V K F) (table : Table V K)
    (ok : check graph table = true) (input : Name V K → α) :
    OrderedExits.run model (forward graph table) input =
      OrderedExits.run model graph (input ∘ Sum.inl) := by
  simp only [OrderedExits.run, OrderedExits.execute, body_bind_proof, pure_bind]
  rw [show (forward graph table).entry = body Sum.inl graph.entry from rfl,
    exec_body_proof model Sum.inl (fun _ _ eq => (Sum.inl.inj eq).symm) _ graph.entry input
      (fun _ => rfl) (fun _ _ => rfl)]
  exact body_congr_proof model _ _ graph.entry _ fun k a s member _ =>
    (iter_forward_proof model graph table ok (none, k, a, Sum.elim s (input ∘ Sum.inr))
      ⟨⟨graph.entry, rfl, member⟩, fun _ => rfl⟩).trans (by simp only [project, Sum.elim_comp_inl])

end Run

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
