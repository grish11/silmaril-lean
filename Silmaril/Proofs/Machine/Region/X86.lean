module

public import Silmaril.Machine.Region.X86.Defs
public import Silmaril.Semantics.Region.Semantic.Thms

@[expose] public section
namespace Silmaril.Machine.Region.X86.Proofs
open Silmaril.Semantics.Region
open Silmaril.X86 (MState Word)
open Silmaril.X86.Decompile

theorem edgeTarget_iff (e : Edge) (l : Nat) : edgeTarget e = some l ↔ e.Target l := by
  cases e <;> simp [edgeTarget, Edge.Target, eq_comm]

theorem instruction_sound {d : Decoded} {s core : Silmaril.X86.State}
    {memory memory' : Silmaril.Process.Memory}
    (hrip : s.rip.toNat = d.addr) (hlen : d.size = (Silmaril.X86.Ext.encode d.instr).length)
    (exec : Silmaril.X86.Ext.exec d.instr s memory = .ok core memory') :
    (instructionTargets d).Allows core.rip.toNat := by
  unfold instructionTargets
  split
  · trivial
  · rename_i hn
    rcases d.edges_sound hrip hlen exec with ⟨e, he, ht⟩ | hr
    · exact List.mem_toFinset.mpr (List.mem_filterMap.mpr
        ⟨e, he, (edgeTarget_iff e _).mpr ht⟩)
    · have hret := Decoded.mem_edges_ret_iff.mp hr
      apply False.elim
      apply hn
      rw [hret]
      rfl

theorem listing_step {r : Silmaril.X86.Decompile.Region} {fuel : Nat} {ds : List Decoded}
    {d : Decoded} {ret : Word} {s t : MState}
    (decoded : r.decode? fuel = some ds) (loaded : r.LoadedIn s.memory)
    (hd : d ∈ ds) (hrip : s.core.rip.toNat = d.addr)
    (step : (system ret).step s [] t) : (instructionTargets d).Allows t.core.rip.toNat := by
  unfold instructionTargets
  split
  · trivial
  · rename_i hn
    have hopt := Silmaril.X86.Ext.stepOpt_eq_some_iff.mpr step.2
    rcases step_nextRip decoded loaded hd hrip hopt with ⟨e, he, ht⟩ | hr
    · exact List.mem_toFinset.mpr (List.mem_filterMap.mpr
        ⟨e, he, (edgeTarget_iff e _).mpr ht⟩)
    · apply False.elim
      apply hn
      rw [hr]
      rfl

/-- The load/frame invariant is a real premise at every internal state. In
particular this does not silently assume stores preserve executable bytes. -/
theorem listing_sound {r : Silmaril.X86.Decompile.Region} {fuel : Nat} {ds : List Decoded}
    {ret : Word} {U X : Nat → Prop} {A D : MState → Prop}
    (decoded : r.decode? fuel = some ds)
    (admit : ∀ s, A s → D s)
    (covered : ∀ s, D s → U s.core.rip.toNat →
      r.LoadedIn s.memory ∧ ∃ d ∈ ds, s.core.rip.toNat = d.addr)
    (preserve : ∀ s es t, D s → U s.core.rip.toNat → (system ret).step s es t →
      U t.core.rip.toNat → D t)
    (targets : ∀ d ∈ ds, ∀ l, (instructionTargets d).Allows l → ¬ U l → X l) :
    Sound (system ret) A U X := by
  apply local_sound (T := system ret) (U := U) (X := X) (D := D) (B := fun s => X s.core.rip.toNat) _ admit (fun _ h => h)
  intro s es t hs hu step
  refine ⟨preserve s es t hs hu step, ?_⟩
  intro out
  obtain ⟨load, d, hd, hrip⟩ := covered s hs hu
  have st : (system ret).step s [] t := ⟨rfl, step.2⟩
  exact targets d hd _ (listing_step decoded load hd hrip st) out
end Silmaril.Machine.Region.X86.Proofs
