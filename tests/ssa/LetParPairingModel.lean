module

import Silmaril.Semantics.Elgot.Parallel.Thms
import Silmaril.Semantics.ElgotMonads.Thms
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

open Silmaril.Elgot

namespace LetParPairingModel

-- Sequential composition adds counts. Parallel pairing takes their maximum.
abbrev Log := Multiplicative Nat
abbrev M := WriterT Log Part

def merge (x y : Log) : Log := Multiplicative.ofAdd (max x.toAdd y.toAdd)

theorem merge_comm (x y : Log) : merge x y = merge y x := by
  exact congrArg Multiplicative.ofAdd (Nat.max_comm _ _)

theorem merge_assoc (x y z : Log) : merge (merge x y) z = merge x (merge y z) := by
  exact congrArg Multiplicative.ofAdd (Nat.max_assoc _ _ _)

theorem merge_one (x : Log) : merge x 1 = x := by
  exact congrArg Multiplicative.ofAdd (Nat.max_zero _)

variable {A B : Type}

def pair (x : M A) (y : M B) : M (A × B) :=
  WriterT.mk <| x.run.bind fun a => y.run.map fun b => ((a.1, b.1), merge a.2 b.2)

theorem mem_pair (x : M A) (y : M B) (c : (A × B) × Log) :
    c ∈ (pair x y).run ↔
      ∃ a ∈ x.run, ∃ b ∈ y.run, ((a.1, b.1), merge a.2 b.2) = c := by
  simp only [pair, WriterT.run_mk, Part.mem_bind_iff, Part.mem_map_iff]

theorem mem_map {C : Type} (f : A → C) (x : M A) (c : C × Log) :
    c ∈ (f <$> x).run ↔ ∃ a ∈ x.run, (f a.1, a.2) = c :=
  Part.mem_map_iff _

def pairing : ParallelPairing M where
  pair := pair
  natural f g x y := by
    apply WriterT.ext
    apply Part.ext
    intro c
    simp only [mem_pair, mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  swap x y := by
    apply WriterT.ext
    apply Part.ext
    intro c
    simp only [mem_pair, mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, a, ha, by simp [Prod.swap, merge_comm]⟩
    · rintro ⟨b, hb, a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, b, hb, rfl⟩, by simp [Prod.swap, merge_comm]⟩
  assoc x y z := by
    apply WriterT.ext
    apply Part.ext
    intro c
    simp only [mem_pair, mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, d, hd, rfl⟩, rfl⟩
      exact ⟨a, ha, _, ⟨b, hb, d, hd, rfl⟩, by rw [merge_assoc]⟩
    · rintro ⟨a, ha, _, ⟨b, hb, d, hd, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, d, hd, rfl⟩, by rw [merge_assoc]⟩
  rightUnit x := by
    apply WriterT.ext
    apply Part.ext
    intro c
    have h : (pure (PUnit.unit : PUnit) : M PUnit).run = Part.some (PUnit.unit, 1) := rfl
    simp only [mem_pair, mem_map, h, Part.mem_some_iff, exists_eq_left,
      merge_one]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ha
    · intro hc
      exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

example : LawfulElgotMonad M := inferInstance

def tick : M PUnit := MonadWriter.tell (Multiplicative.ofAdd 1)

theorem run_parallel : (pairing.pair tick tick).run =
    Part.some ((PUnit.unit, PUnit.unit), Multiplicative.ofAdd 1) := by
  simp [pairing, pair, tick, merge]

theorem run_sequential : (tick >>= fun a => tick >>= fun b => pure (a, b)).run =
    Part.some ((PUnit.unit, PUnit.unit), Multiplicative.ofAdd 2) := by
  simp only [tick, WriterT.run_bind, WriterT.run_tell, WriterT.run_pure, pure_bind, map_pure, mul_one]
  rfl

theorem parallel_ne_sequential :
    pairing.pair tick tick ≠ (tick >>= fun a => tick >>= fun b => pure (a, b)) := by
  intro h
  have hr := congrArg WriterT.run h
  rw [run_parallel, run_sequential] at hr
  have hlog := congrArg (fun p => (Prod.snd p : Log).toAdd) (Part.some_injective hr)
  contradiction

-- Both orders have the same result for two identical branches.
example : pairing.pair tick tick ≠ (tick >>= fun b => tick >>= fun a => pure (a, b)) := by
  refine fun h => parallel_ne_sequential (h.trans ?_)
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  exact congrArg pure (Subsingleton.elim _ _)

theorem no_interchange :
    pairing.pair (tick >>= (pure : PUnit → M PUnit)) ((pure () : M PUnit) >>= fun _ => tick) ≠
      (pairing.pair tick (pure ()) >>= fun p => pairing.pair (pure p.1) tick) := by
  simpa only [bind_pure, pure_bind, ParallelPairing.pair_pure_right,
    ParallelPairing.pair_pure_left, ← bind_pure_comp, bind_assoc] using parallel_ne_sequential

end LetParPairingModel
