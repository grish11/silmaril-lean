module

public import Silmaril.Numeric.UnixInterop.Defs
public import Silmaril.Numeric.UnixRepresentation.Binary64.Defs
import Silmaril.Numeric.UnixRepresentation.Thms
import Silmaril.Numeric.UnixRepresentation.Binary64.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.Proofs.Numeric.UnixInterop

open Silmaril.Numeric.UnixInterop
open Silmaril.Numeric.UnixClock Silmaril.Numeric.TimeZone Silmaril.Numeric.Timestamp
open Silmaril.Numeric.UnixRepresentation Silmaril.Numeric.Ieee754
open Set

private theorem tickSeconds_pos (unit : TickUnit) : 0 < tickSeconds unit := by
  cases unit <;> norm_num [tickSeconds, TickUnit.nanosecondsPerTick]

private theorem discrepancy_le (a b p q : ℝ) :
    |p - q| ≤ |a - b| + |a - p| + |b - q| := by
  have h₁ := abs_sub_le p a q
  have h₂ := abs_sub_le a b q
  rw [abs_sub_comm p a] at h₁
  linarith

theorem wordFloor_error {format : WordFormat} {unit : TickUnit} {stamp : UnixTime}
    {payload : format.Payload} (encoded : format.encode stamp unit .floor = .ok payload) :
    let err := unixSeconds stamp - unixSeconds (format.decode .utcInstant unit payload)
    0 ≤ err ∧ err < tickSeconds unit := by
  have ⟨h₀, h₁⟩ := quantize_floor (WordFormat.encode_eq_ok_iff.mp encoded)
  have h₀' : (0 : ℝ) ≤ (stamp.denote.ticks : ℝ) -
      ((format.decode .utcInstant unit payload).denote.ticks : ℝ) := by exact_mod_cast h₀
  have h₁' : (stamp.denote.ticks : ℝ) -
      ((format.decode .utcInstant unit payload).denote.ticks : ℝ) <
      (unit.nanosecondsPerTick : ℝ) := by exact_mod_cast h₁
  simpa only [unixSeconds, tickSeconds, ← sub_div] using
    And.intro (div_nonneg h₀' (by norm_num : (0 : ℝ) ≤ 1000000000))
      (div_lt_div_of_pos_right h₁' (by norm_num : (0 : ℝ) < 1000000000))

theorem wordFloor_discrepancy {a b : Convention} (t : ↑(a.domain ∩ b.domain))
    {sa sb : UnixTime} {fa fb : WordFormat} {ua ub : TickUnit}
    {pa : fa.Payload} {pb : fb.Payload}
    (ga : unixSeconds sa = a.forward ⟨t.val, t.property.1⟩)
    (gb : unixSeconds sb = b.forward ⟨t.val, t.property.2⟩)
    (ea : fa.encode sa ua .floor = .ok pa) (eb : fb.encode sb ub .floor = .ok pb) :
    |unixSeconds (fa.decode .utcInstant ua pa) - unixSeconds (fb.decode .utcInstant ub pb)| <
      |a.forward ⟨t.val, t.property.1⟩ - b.forward ⟨t.val, t.property.2⟩| +
        tickSeconds ua + tickSeconds ub := by
  obtain ⟨ha₀, ha₁⟩ := wordFloor_error ea
  obtain ⟨hb₀, hb₁⟩ := wordFloor_error eb
  have h := discrepancy_le (unixSeconds sa) (unixSeconds sb)
    (unixSeconds (fa.decode .utcInstant ua pa)) (unixSeconds (fb.decode .utcInstant ub pb))
  rw [abs_of_nonneg ha₀, abs_of_nonneg hb₀, ga, gb] at h
  linarith

private theorem count_seconds (stamp : UnixTime) (unit : TickUnit) :
    (Binary64.count stamp unit : ℝ) * tickSeconds unit = unixSeconds stamp := by
  cases unit <;>
    norm_num [Binary64.count, tickSeconds, unixSeconds, TickUnit.nanosecondsPerTick, Rat.cast_div] <;>
    ring

theorem binary64Rne_error {unit : TickUnit} {stamp : UnixTime} {payload : F64}
    (encoded : Binary64.encodeRne stamp unit = .ok payload) :
    ∃ q : ℚ, payload.toRat? = some q ∧
      |unixSeconds stamp - (q : ℝ) * tickSeconds unit| ≤
        ((Binary64.ulp (Binary64.count stamp unit) / 2 : ℚ) : ℝ) * tickSeconds unit := by
  obtain ⟨q, decoded, bound⟩ := Binary64.encodeRne_halfUlp encoded
  refine ⟨q, decoded, ?_⟩
  have h : |(Binary64.count stamp unit : ℝ) - (q : ℝ)| ≤
      ((Binary64.ulp (Binary64.count stamp unit) / 2 : ℚ) : ℝ) := by exact_mod_cast bound
  rw [← count_seconds stamp unit, ← sub_mul, abs_mul, abs_of_pos (tickSeconds_pos unit)]
  exact mul_le_mul_of_nonneg_right h (tickSeconds_pos unit).le

theorem binary64Rne_discrepancy {a b : Convention} (t : ↑(a.domain ∩ b.domain))
    {sa sb : UnixTime} {ua ub : TickUnit} {pa pb : F64}
    (ga : unixSeconds sa = a.forward ⟨t.val, t.property.1⟩)
    (gb : unixSeconds sb = b.forward ⟨t.val, t.property.2⟩)
    (ea : Binary64.encodeRne sa ua = .ok pa) (eb : Binary64.encodeRne sb ub = .ok pb) :
    ∃ qa qb : ℚ, pa.toRat? = some qa ∧ pb.toRat? = some qb ∧
      |(qa : ℝ) * tickSeconds ua - (qb : ℝ) * tickSeconds ub| ≤
        |a.forward ⟨t.val, t.property.1⟩ - b.forward ⟨t.val, t.property.2⟩| +
          ((Binary64.ulp (Binary64.count sa ua) / 2 : ℚ) : ℝ) * tickSeconds ua +
          ((Binary64.ulp (Binary64.count sb ub) / 2 : ℚ) : ℝ) * tickSeconds ub := by
  obtain ⟨qa, da, ha⟩ := binary64Rne_error ea
  obtain ⟨qb, db, hb⟩ := binary64Rne_error eb
  refine ⟨qa, qb, da, db, ?_⟩
  have h := discrepancy_le (unixSeconds sa) (unixSeconds sb)
    ((qa : ℝ) * tickSeconds ua) ((qb : ℝ) * tickSeconds ub)
  rw [ga, gb] at h
  rw [ga] at ha
  rw [gb] at hb
  linarith

end Silmaril.Proofs.Numeric.UnixInterop
