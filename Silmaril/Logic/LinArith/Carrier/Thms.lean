module

public import Silmaril.Logic.LinArith.Carrier.Defs
public import Silmaril.Logic.LinArith.Thms

@[expose] public section

/-!
# Farkas certificates over WIT words: results

* **`farkasCheck_sound`**: `Accepts farkasCheck ⊆ Infeasible`, from the existing
  `LinArith.checkCert_sound`: a system with an accepted multiplier list has no solution over any
  ordered field. Soundness is the existential projection over certificates; nothing is claimed
  about completeness.
* `decodeSystem_encode`: the reading loses nothing on systems in range, and `IneqW.decode` is
  injective (`IneqW.decode_injective`).
-/

namespace Silmaril.Logic.LinArith.Carrier

open Silmaril.Logic.SAT.Carrier (Accepts)

/-- **Accepted systems are infeasible over every ordered field.** -/
theorem farkasCheck_sound : Accepts farkasCheck ⊆ Infeasible :=
  fun _ ⟨_, h⟩ K _ _ _ => checkCert_sound (K := K) h

theorem toNat_ofNat_32 {n : ℕ} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toInt_ofInt_64 {a : ℤ} (h : InRange64 a) : (BitVec.ofInt 64 a).toInt = a := by
  obtain ⟨h1, h2⟩ := h
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le_mul_two (by simp; omega) (by simp; omega)

theorem IneqW.decode_encode {r : Ineq} (h : IneqInRange r) : (IneqW.encode r).decode = r := by
  obtain ⟨cs, b⟩ := r
  obtain ⟨hc, hb⟩ := h
  simp only [IneqW.encode, IneqW.decode, List.map_map, toInt_ofInt_64 hb, Ineq.mk.injEq, and_true]
  conv => rhs; rw [← List.map_id cs]
  exact List.map_congr_left fun p hp => by
    obtain ⟨j, a⟩ := p
    simp [toNat_ofNat_32 (hc _ hp).1, toInt_ofInt_64 (hc _ hp).2]

/-- **The reading is lossless on systems in range.** -/
theorem decodeSystem_encode {S : System} (h : ∀ r ∈ S, IneqInRange r) :
    decodeSystem (S.map IneqW.encode) = S := by
  simp only [decodeSystem, List.map_map]
  conv => rhs; rw [← List.map_id S]
  exact List.map_congr_left fun r hr => IneqW.decode_encode (h r hr)

theorem IneqW.decode_injective : Function.Injective IneqW.decode := by
  rintro ⟨c, b⟩ ⟨c', b'⟩ h
  simp only [IneqW.decode, Ineq.mk.injEq] at h
  obtain ⟨hc, hb⟩ := h
  have hb' : b = b' := BitVec.toInt_inj.1 hb
  have hc' : c = c' := by
    refine List.map_injective_iff.2 (fun p q hpq => ?_) hc
    obtain ⟨j, a⟩ := p
    obtain ⟨j', a'⟩ := q
    simp only [Prod.mk.injEq] at hpq ⊢
    exact ⟨BitVec.eq_of_toNat_eq hpq.1, BitVec.toInt_inj.1 hpq.2⟩
  rw [hb', hc']

end Silmaril.Logic.LinArith.Carrier
