module

public import Silmaril.Semantics.ConcurrentTrace.EventSync.Defs

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.EventSync

open Silmaril.Semantics.ConcurrentTrace
open Silmaril.Semantics.ConcurrentTrace.EventSync

universe u v

variable {T : Type u} {E : Type v}

theorem length_ofWord (w : Word T E) : (lengthHom (ofWord w)).toAdd = w.length := by
  induction w with
  | nil => simp [ofWord_nil, map_one]
  | cons a w ih =>
    rw [ofWord_cons, map_mul]
    change 1 + (lengthHom (ofWord w)).toAdd = w.length + 1
    rw [ih, Nat.add_comm]

theorem dvd_antisymm {x y : Trace T E} (hxy : x ∣ y) (hyx : y ∣ x) : x = y := by
  obtain ⟨z, hy⟩ := hxy
  obtain ⟨v, hx⟩ := hyx
  have lengthMul (p q : Trace T E) :
      (lengthHom (p * q)).toAdd = (lengthHom p).toAdd + (lengthHom q).toAdd := by
    rw [map_mul]
    rfl
  have hyLen := congrArg (fun p => (lengthHom p).toAdd) hy
  have hxLen := congrArg (fun p => (lengthHom p).toAdd) hx
  simp only [lengthMul] at hyLen hxLen
  obtain ⟨w, rfl⟩ := ofWord_surjective z
  have hw : w.length = 0 := by rw [← length_ofWord]; omega
  rw [List.length_eq_zero_iff.mp hw, ofWord_nil, mul_one] at hy
  exact hy.symm

variable {T' E' A : Type u} {Event : Type u} {Thread : Type u}

theorem alloc_mapTrace (f : Thread → T') (hf : Function.Injective f) (g : Event → E')
    (x : ThreadTrace.Alloc Thread (FreeMonoid (Letter Thread Event)) A) :
    ThreadTrace.Alloc.mapOutput (mapTrace f hf g) (ThreadTrace.Alloc.mapOutput quotientOutput x) =
      ThreadTrace.Alloc.mapOutput quotientOutput
        (ThreadTrace.Alloc.mapOutput (FreeMonoid.map (Letter.map f g)) x) := by
  apply ThreadTrace.Alloc.ext
  intro t used
  ext ⟨⟨a, final⟩, v⟩
  simp only [ThreadTrace.Alloc.mem_mapOutput]
  constructor
  · rintro ⟨q, ⟨w, hw, rfl⟩, h⟩
    exact ⟨FreeMonoid.map (Letter.map f g) w, ⟨w, hw, rfl⟩,
      (mapTrace_ofWord f hf g w.toList).symm.trans h⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
    exact ⟨quotientOutput w, ⟨w, hw, rfl⟩, (mapTrace_ofWord f hf g w.toList).trans h⟩

end Silmaril.Proofs.Semantics.ConcurrentTrace.EventSync
