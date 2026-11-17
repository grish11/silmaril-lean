module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintPutc
public import Silmaril.Raw.Elf.Link.Dyn.Streams.Rep

/-! # The stream laws of `TailImps` hold for the concrete representation (non-vacuity)

`TailImps` (the world's part of `main`'s tail on the stdin tier) asks, besides the imports'
contracts, for laws of the stream representation: `PutcLaw`, `StreamsDisj`, `PrivApart`,
`stdout`'s footprint outside the kept memory, `stdout` not wrapping, and `stdout ≠ stderr`.
They all hold for the slot representation `Streams.Total.slotRep` (the one whose contracts are
shown total in `Streams.Total`), with `stdout` and `stderr` in two distinct slots and a world
whose kept memory avoids the library's arena (`slot_tailLaws`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total

theorem slot_putcLaw (E : Env) (hS : E.S = slotRep) : PutcLaw E := by
  refine ⟨?_, fun m m' _ _ _ _ _ => by rw [hS]; rfl⟩
  intro m f st p e h hp he hlt
  rw [hS] at h
  rw [show f + 0x30#64 = f + BitVec.ofNat 64 0x30 from rfl, loadN_zero h (Or.inr rfl)] at he
  cases he
  simp at hlt

theorem slot_footR {m : Memory} {f : Word} {st : St} (h : fileR m f st) {a : Nat} (ha : footR m f a) :
    f.toNat ≤ a ∧ a < f.toNat + S0 := by
  have hl := lenAt_of h
  obtain ⟨-, ⟨-, -, hS⟩, -⟩ := h
  unfold footR at ha; rw [hl] at ha
  omega

theorem slot_streamsDisj (E : Env) (hS : E.S = slotRep) : StreamsDisj E := by
  intro m f f' st st' a hne hf hf' ha hb
  rw [hS] at hf hf' ha hb
  have h1 := slot_footR hf ha
  have h2 := slot_footR hf' hb
  obtain ⟨k, -, hk⟩ := hf.1
  obtain ⟨k', -, hk'⟩ := hf'.1
  have hkk : k ≠ k' := fun he => hne (BitVec.eq_of_toNat_eq (by rw [hk, hk', he]))
  unfold S0 at h1 h2 hk hk'
  rcases Nat.lt_or_gt_of_ne hkk with hl | hl
  · have : k * 0x100000 + 0x100000 ≤ k' * 0x100000 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
    omega
  · have : k' * 0x100000 + 0x100000 ≤ k * 0x100000 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
    omega

/-- **The stream laws of `TailImps` for the slot representation**: with `stdout` and `stderr`
in two distinct slots, and a world whose kept memory avoids the arena. -/
theorem slot_tailLaws (E : Env) (hS : E.S = slotRep) (hout : IsSlot E.stdoutF) (hne : E.stdoutF ≠ E.stderrF)
    (W : World) (hW : ∀ a, W.Kept a → ¬ Arena a) :
    PutcLaw E ∧ StreamsDisj E ∧ PrivApart E W ∧
      (∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a) ∧
      E.stdoutF.toNat + 0x38 < 2 ^ 64 ∧ E.stdoutF ≠ E.stderrF := by
  refine ⟨slot_putcLaw E hS, slot_streamsDisj E hS, fun m a hK hp => ?_, fun m st a hf ha hK => ?_, ?_, hne⟩
  · rw [hS] at hp; exact hW a hK hp
  · rw [hS] at hf ha
    exact hW a hK (slotRep.foot_priv m _ st a hf ha)
  · have := slot_lt hout
    unfold A0 K0 S0 at this
    omega

end Silmaril.Elf.Link.Dyn.Sha256sum
