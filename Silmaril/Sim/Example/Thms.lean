module

public import Silmaril.Sim.Example.Defs
public import Silmaril.Sim.Institution.Thms

/-!
# The toy ISA: soundness and transfer (header, short proofs inline)

PROVED: `sim_sound` (the partial simulator is sound for the relational reference, although
`af` is undefined in the ISA and unknown to the simulator), `φ_angelicMono`, `sim_sat` (the
simulator satisfies `φ`), and `ref_sat` (the ISA satisfies `φ`, by `Institution.transfer`
along the identity signature morphism).
-/

@[expose] public section

namespace Silmaril.Sim.Example

open Silmaril.Sim Silmaril.Sim.Institution

private theorem r0_of_le {p : PState Loc Nat} {b : Loc → Nat} {n : Nat}
    (hb : p ⊑ ref.view b) (hn : p .r0 = some n) : b .r0 = n :=
  Option.some.inj (hb .r0 n hn)

private theorem sound_inc : sim.SoundAt ref (.inl .inc) := by
  intro p p' b hb hs
  obtain ⟨n, hn, hp'⟩ : ∃ n, p .r0 = some n ∧ p' = incOut n p := hs
  have hb0 : b .r0 = n := r0_of_le hb hn
  refine ⟨fun | .r0 => b .r0 + 1 | .r1 => b .r1 | .af => 0, ⟨rfl, rfl⟩, ?_⟩
  intro l v hv
  have hv' : incOut n p l = some v := hp' ▸ hv
  cases l with
  | r0 =>
    have hv0 : n + 1 = v := Option.some.inj hv'
    show some (b .r0 + 1) = some v
    rw [hb0, hv0]
  | r1 => exact hb .r1 v hv'
  | af => exact absurd hv' (by simp [incOut])

private theorem sound_mov : sim.SoundAt ref (.inl .mov) := by
  intro p p' b hb hs
  obtain ⟨n, hn, hp'⟩ : ∃ n, p .r0 = some n ∧ p' = movOut n p := hs
  have hb0 : b .r0 = n := r0_of_le hb hn
  refine ⟨fun | .r0 => b .r0 | .r1 => b .r0 | .af => b .af, ⟨rfl, rfl, rfl⟩, ?_⟩
  intro l v hv
  have hv' : movOut n p l = some v := hp' ▸ hv
  cases l with
  | r0 => exact (congrArg some hb0).trans hv'
  | r1 => exact (congrArg some hb0).trans hv'
  | af => exact hb .af v hv'

theorem sim_sound : sim.Sound ref := by
  intro c p p' b hb hs
  rcases c with c | e
  · cases c with
    | inc => exact sound_inc p p' b hb hs
    | mov => exact sound_mov p p' b hb hs
  · exact e.elim

theorem φ_angelicMono : φ.AngelicMono :=
  ⟨⟨trivial, trivial, trivial⟩, fun _ _ _ hle h => hle _ _ h⟩

/-- The simulator satisfies `φ` (as a model of the institution). -/
theorem sim_sat : sat (Mod.of (S := sig) sim.toMachine) φ := by
  intro p hp
  refine ⟨movOut 1 (incOut 0 p), ⟨incOut 0 p, ⟨0, hp, rfl⟩, movOut 1 (incOut 0 p),
    ⟨1, rfl, rfl⟩, rfl⟩, rfl⟩

/-- **The ISA satisfies `φ`**, transferred from the simulator. -/
theorem ref_sat : sat (Mod.of (S := sig) ref) φ := by
  have h := transfer (Sig.Hom.id sig) (A := Mod.of (S := sig) sim.toMachine)
    (B := Mod.of (S := sig) ref) sim_sound.sound φ_angelicMono sim_sat
  rwa [Sen.map_id] at h

end Silmaril.Sim.Example

end
