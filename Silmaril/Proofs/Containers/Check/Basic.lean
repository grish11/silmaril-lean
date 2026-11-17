module

public import Silmaril.Containers.Check.Defs
public import Silmaril.Containers.Precondition.Thms
public import Silmaril.Semantics.Acceptors.Thms

/-!
# Proofs: container obligations as consequence systems and acceptors

Proofs for `Silmaril.Containers.Check.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Check

open Silmaril.Containers Silmaril.Containers.Check Silmaril.Consequence

variable {I P E : Type}

theorem checkSys_sound_iff (R : Runtime I P E) (check : I → Bool) (φ : Spec E) :
    System.Sound (checkSys check φ) (vsys R) ↔ Silmaril.Accept.Sound check (vset R φ) := by
  constructor
  · intro h i hc
    exact h i φ ⟨hc, rfl⟩
  · rintro h i ψ ⟨hc, rfl⟩
    exact h i hc

theorem foldl_process (ok : E → Bool) (cs : List (List (Obs E))) (b : Bool) :
    cs.foldl (vmonitor ok).process b = (b && (cs.flatMap id).all (Obs.ok ok)) := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, List.flatMap_cons, List.all_append, id]
    simp [vmonitor, Bool.and_assoc]

theorem vmonitor_correctFold (ok : E → Bool) : (vmonitor ok).CorrectFold (vlang ok) := by
  intro cs
  show (cs.foldl (vmonitor ok).process true) = Silmaril.Acceptor.member (vlang ok) _
  rw [foldl_process, Bool.true_and]
  show _ = decide ((cs.flatMap id).all (Obs.ok ok) = true)
  cases (cs.flatMap id).all (Obs.ok ok) <;> rfl

theorem vmonitor_correctInterleaved (ok : E → Bool) :
    (vmonitor ok).CorrectInterleaved (vlang ok) :=
  Silmaril.Acceptor.correctInterleaved_of_correctFold (fun _ => rfl)
    (Silmaril.Acceptor.ResetSound.of_eq fun _ => rfl) (vmonitor_correctFold ok)

theorem mem_vlang {ok : E → Bool} {w : List (Obs E)} :
    w ∈ vlang ok ↔ ∀ x ∈ w, Obs.ok ok x = true := by
  show w.all (Obs.ok ok) = true ↔ _
  exact List.all_eq_true

theorem vlang_iff (ok : E → Bool) (b : Beh E) :
    (Spec.noUB b ∧ Spec.always (fun e => ok e = true) b) ↔
      ∀ w, ObsPrefix b w → w ∈ vlang ok := by
  constructor
  · rintro ⟨hu, ha⟩ w (⟨t, ht, rfl⟩ | ⟨t, s, rfl, rfl⟩)
    · refine mem_vlang.2 fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact ha t ht e he
    · refine mem_vlang.2 fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        exact ha t (List.prefix_refl t) e he
      · rw [List.mem_singleton.1 hx]
        cases s <;> first | rfl | exact hu.elim
  · intro h
    refine ⟨?_, fun t ht e he => ?_⟩
    · rcases b with ⟨t, s⟩ | _ | _ | _ <;> try trivial
      cases s with
      | undefined u =>
        have := mem_vlang.1 (h _ (.inr ⟨t, _, rfl, rfl⟩)) (.stop (.undefined u)) (by simp)
        cases this
      | _ => trivial
    · exact mem_vlang.1 (h _ (.inl ⟨t, ht, rfl⟩)) (.ev e) (List.mem_map_of_mem he)

end Silmaril.Proofs.Containers.Check
