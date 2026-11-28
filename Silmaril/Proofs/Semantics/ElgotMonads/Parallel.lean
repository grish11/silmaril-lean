module

public import Silmaril.Semantics.ElgotMonads.Parallel.Defs

/-! Proofs of coherence for bind-induced pairing and its finite-success instances. -/

public section

namespace Silmaril.Proofs.Semantics.ElgotMonads.Parallel

open Silmaril.Elgot
open scoped Silmaril.Elgot.Nondet

universe u

variable {A B : Type u}

theorem part_mem_left (x : _root_.Part A) (y : _root_.Part B) (p : A × B) :
    p ∈ ParallelPairing.bindPair x y ↔ p.1 ∈ x ∧ p.2 ∈ y := by
  obtain ⟨a, b⟩ := p
  change (a, b) ∈ x.bind (fun a' => y.bind fun b' => _root_.Part.some (a', b')) ↔ _
  simp [_root_.Part.mem_bind_iff, _root_.Part.mem_some_iff, Prod.mk.injEq]

theorem part_mem_right (x : _root_.Part A) (y : _root_.Part B) (p : A × B) :
    p ∈ (y >>= fun b => x >>= fun a => pure (a, b)) ↔ p.1 ∈ x ∧ p.2 ∈ y := by
  obtain ⟨a, b⟩ := p
  change (a, b) ∈ y.bind (fun b' => x.bind fun a' => _root_.Part.some (a', b')) ↔ _
  simp [_root_.Part.mem_bind_iff, _root_.Part.mem_some_iff, Prod.mk.injEq, and_comm]

theorem set_mem_left (x : SetM A) (y : SetM B) (p : A × B) :
    p ∈ₘ ParallelPairing.bindPair x y ↔ p.1 ∈ₘ x ∧ p.2 ∈ₘ y := by
  obtain ⟨a, b⟩ := p
  simp only [ParallelPairing.bindPair, Nondet.mem_bind_iff, Nondet.mem_pure_iff]
  simp

theorem set_mem_right (x : SetM A) (y : SetM B) (p : A × B) :
    p ∈ₘ (y >>= fun b => x >>= fun a => pure (a, b)) ↔ p.1 ∈ₘ x ∧ p.2 ∈ₘ y := by
  obtain ⟨a, b⟩ := p
  simp only [Nondet.mem_bind_iff, Nondet.mem_pure_iff]
  simp [and_comm]

end Silmaril.Proofs.Semantics.ElgotMonads.Parallel
