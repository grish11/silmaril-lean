module

public import Silmaril.Semantics.Region.Examples.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Examples.Proofs

theorem invariant : Local machine support domain (fun s => s.1 = 2) := by
  intro s es t hd _ step
  cases step with
  | restrict b => simp [machine, support, domain]
  | indirect b =>
    have hb : b = true := by simpa [domain] using hd
    subst b
    simp [machine, support, domain]

theorem region_valid : Valid machine (fun _ => True) (fun s => s.1 = 0) support 0 {2} := by
  refine ⟨trivial, .inl rfl, ⟨(0, false), rfl⟩, fun _ h => h, fun _ _ => trivial, ?_⟩
  exact local_sound invariant (fun s h => .inl h) (fun _ h => Finset.mem_singleton.mpr h)

theorem local_failure : ¬ Sound machine (fun s => s.1 = 1) (fun l => l = 1) (fun l => l = 2) := by
  intro h
  have bad : FirstExit machine (fun l => l = 1) (1, false) [] (3, false) :=
    .leave rfl (.indirect false) (by decide)
  exact (by decide : (3 : Nat) ≠ 2) (h _ _ _ rfl bad)

theorem restricted_success : Sound machine (fun s => s = (1, true)) (fun l => l = 1)
    (fun l => l = 2) := by
  apply local_sound (T := machine) (U := fun l => l = 1) (X := fun l => l = 2)
    (D := fun s => s = (1, true)) (B := fun s => s.1 = 2) _
    (fun _ h => h) (fun _ h => h)
  intro s es t hd _ step
  cases step with
  | restrict b => cases hd
  | indirect b =>
    have hb : b = true := congrArg Prod.snd hd
    subst b
    simp [machine]

theorem empty_exits_loop : Sound loop (fun _ => True) (fun l => l = 0) (fun _ => False) := by
  apply local_sound (T := loop) (U := fun l => l = 0) (X := fun _ => False)
    (D := fun _ => True) (B := fun _ => False) _ (fun _ _ => trivial)
    (fun _ h => h)
  intro s es t _ _ step
  exact ⟨fun _ => trivial, fun out => out rfl⟩

theorem loop_diverges : Diverges loop (fun l => l = 0) () := by
  refine ⟨fun _ => (), fun _ => [], rfl, ?_⟩
  intro n
  exact ⟨rfl, rfl, rfl⟩

theorem erased_incompatible :
    witnessModel.erase.Reg () () false ∅ ∧ witnessModel.erase.Reg () () true ∅ ∧
      ¬ ∃ ss, witnessModel.Reg () () ss false ∅ ∧ witnessModel.Reg () () ss true ∅ := by
  refine ⟨⟨{false}, rfl⟩, ⟨{true}, rfl⟩, ?_⟩
  rintro ⟨ss, hf, ht⟩
  have h : ({false} : Finset Bool) = {true} := hf.symm.trans ht
  have : false ∈ ({true} : Finset Bool) := h ▸ Finset.mem_singleton_self false
  simp at this

theorem nonvacuity : ¬ Valid machine (fun _ => True) (fun _ => False) support 0 {2} := by
  rintro ⟨_, _, ⟨s, impossible⟩, _⟩
  exact impossible

end Silmaril.Semantics.Region.Examples.Proofs
