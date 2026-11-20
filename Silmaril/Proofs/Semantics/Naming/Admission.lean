module

public import Silmaril.Semantics.Naming.Admission.Defs
public import Silmaril.Semantics.Naming.Thms

public section

namespace Silmaril.Proofs.Semantics.Naming.Admission

open Silmaril.Semantics.Naming

variable {Name Payload : Type} [DecidableEq Name] [DecidableEq Payload]

private theorem single_spec (read : Name → Option Payload) (write : Name × Payload) :
    match admitOne read write with
    | .ok updated => graph updated = union (graph read) (listed [write])
    | .error name => name ∈ collisions (union (graph read) (listed [write])) := by
  rcases write with ⟨name, payload⟩
  cases present : read name with
  | none =>
    simp only [admitOne, present]
    ext queried observed
    by_cases same : queried = name
    · subst queried
      simp [graph, union, listed, present, eq_comm]
    · simp [graph, union, listed, same]
  | some stored =>
    by_cases same : stored = payload
    · subst stored
      simp only [admitOne, present, ↓reduceIte]
      ext queried observed
      by_cases hit : queried = name
      · subst queried
        simp [graph, union, listed, present, eq_comm]
      · simp [graph, union, listed, hit]
    · have collides : name ∈ collisions (union (graph read) (listed [(name, payload)])) :=
        ⟨stored, payload, .inl present, .inr (by simp [listed]), same⟩
      simpa [admitOne, present, same] using collides

omit [DecidableEq Name] [DecidableEq Payload] in
private theorem union_cons (read : Name → Option Payload) (write : Name × Payload) (rest : List (Name × Payload)) :
    union (union (graph read) (listed [write])) (listed rest) = union (graph read) (listed (write :: rest)) := by
  ext name payload
  simp [union, listed, or_assoc]

theorem admit_spec (read : Name → Option Payload) (writes : List (Name × Payload)) :
    match admit read writes with
    | .ok updated => graph updated = union (graph read) (listed writes)
    | .error name => name ∈ collisions (union (graph read) (listed writes)) := by
  induction writes generalizing read with
  | nil =>
    change graph read = union (graph read) (listed [])
    ext name payload
    simp [union, listed]
  | cons write rest ih =>
    have single := single_spec read write
    cases step : admitOne read write with
    | ok updated =>
      simp only [step] at single
      simpa only [admit, step, single, union_cons] using ih updated
    | error name =>
      simp only [step] at single
      obtain ⟨left, right, first, second, conflict⟩ := single
      have incl : Subset (union (graph read) (listed [write])) (union (graph read) (listed (write :: rest))) :=
        fun _ _ hit => hit.elim Or.inl (fun member => Or.inr (List.mem_cons.mpr (.inl (List.mem_singleton.mp member))))
      simpa only [admit, step] using
        (show name ∈ collisions (union (graph read) (listed (write :: rest))) from
          ⟨left, right, incl first, incl second, conflict⟩)

theorem admit_exists_iff (read : Name → Option Payload) (writes : List (Name × Payload)) :
    (∃ updated, admit read writes = .ok updated) ↔ Binding (union (graph read) (listed writes)) := by
  have spec := admit_spec read writes
  cases accepted : admit read writes with
  | ok updated =>
    simp only [accepted] at spec
    rw [← spec]
    exact ⟨fun _ => graph_binding _, fun _ => ⟨updated, rfl⟩⟩
  | error name =>
    simp only [accepted] at spec
    constructor
    · rintro ⟨_, impossible⟩
      contradiction
    · intro bound
      obtain ⟨_, _, first, second, different⟩ := spec
      exact (different (bound first second)).elim

end Silmaril.Proofs.Semantics.Naming.Admission
