module

public import Silmaril.Numeric.UnixInterop.Defs
public import Silmaril.Numeric.UnixRepresentation.Binary64.Defs
import Silmaril.Proofs.Numeric.UnixInterop.CodecError
import Silmaril.Proofs.Numeric.UnixInterop.LocalReading

public section

namespace Silmaril.Numeric.UnixInterop

open TimeZone UnixClock Timestamp UnixRepresentation Ieee754
open Set

/-- Exact conversion succeeds precisely for the stamp denoting the input seconds. -/
theorem exactNanoseconds_eq_some_iff {seconds : ℝ} {stamp : UnixTime} :
    exactNanoseconds? seconds = some stamp ↔ unixSeconds stamp = seconds :=
  Proofs.Numeric.UnixInterop.exactNanoseconds_eq_some_iff

/-- Forward conversion composes exact clock normalization and the zone's wall conversion. -/
theorem readWall_eq_some_iff {clock : Convention} {rules : Rules} {t : clock.domain}
    {wall : WallTime} :
    readWall? clock rules t = some wall ↔
      ∃ stamp, unixSeconds stamp = clock.forward t ∧ rules.toLocal? stamp = some wall :=
  Proofs.Numeric.UnixInterop.readWall_eq_some_iff

/-- A supported physical input has a wall reading exactly when its nominal reading is on
    the nanosecond grid and the zone rules support the corresponding stamp. -/
theorem readWall_supported_iff {clock : Convention} {rules : Rules} {t : clock.domain} :
    (readWall? clock rules t).isSome = true ↔
      ∃ stamp, unixSeconds stamp = clock.forward t ∧ rules.Supports stamp :=
  Proofs.Numeric.UnixInterop.readWall_supported_iff

/-- The composed inverse includes exactly the supported preimages of the wall reading. -/
theorem mem_physicalCandidates_iff {clock : Convention} {rules : Rules} {wall : WallTime}
    {t : ℝ} :
    t ∈ physicalCandidates clock rules wall ↔
      ∃ h : t ∈ clock.domain, readWall? clock rules ⟨t, h⟩ = some wall :=
  Proofs.Numeric.UnixInterop.mem_physicalCandidates_iff

/-- A civil reading is a forward result exactly when it encodes a wall reading
    whose composed inverse contains this physical instant. -/
theorem readCivil_eq_some_iff {clock : Convention} {rules : Rules} {t : clock.domain}
    {civil : CivilReading} :
    readCivil? clock rules t = some civil ↔
      ∃ wall, civil.toWall? = some wall ∧ t.val ∈ physicalCandidates clock rules wall :=
  Proofs.Numeric.UnixInterop.readCivil_eq_some_iff

/-- A successful integer floor encoding loses a nonnegative amount below one payload tick,
    measured in nominal seconds. -/
theorem wordFloor_error {format : WordFormat} {unit : TickUnit} {stamp : UnixTime}
    {payload : format.Payload} (encoded : format.encode stamp unit .floor = .ok payload) :
    let err := unixSeconds stamp - unixSeconds (format.decode .utcInstant unit payload)
    0 ≤ err ∧ err < tickSeconds unit :=
  Proofs.Numeric.UnixInterop.wordFloor_error encoded

/-- On common physical support, exact-grid readings with successful integer floor encodings
    differ after decoding by less than the clock discrepancy plus both payload tick lengths. -/
theorem wordFloor_discrepancy {a b : Convention} (t : ↑(a.domain ∩ b.domain))
    {sa sb : UnixTime} {fa fb : WordFormat} {ua ub : TickUnit}
    {pa : fa.Payload} {pb : fb.Payload}
    (ga : unixSeconds sa = a.forward ⟨t.val, t.property.1⟩)
    (gb : unixSeconds sb = b.forward ⟨t.val, t.property.2⟩)
    (ea : fa.encode sa ua .floor = .ok pa) (eb : fb.encode sb ub .floor = .ok pb) :
    |unixSeconds (fa.decode .utcInstant ua pa) - unixSeconds (fb.decode .utcInstant ub pb)| <
      |a.forward ⟨t.val, t.property.1⟩ - b.forward ⟨t.val, t.property.2⟩| +
        tickSeconds ua + tickSeconds ub :=
  Proofs.Numeric.UnixInterop.wordFloor_discrepancy t ga gb ea eb

/-- A finite binary64 RNE encoding has a half-ULP error after normalizing the payload
    and the local spacing to nominal seconds. -/
theorem binary64Rne_error {unit : TickUnit} {stamp : UnixTime} {payload : F64}
    (encoded : Binary64.encodeRne stamp unit = .ok payload) :
    ∃ q : ℚ, payload.toRat? = some q ∧
      |unixSeconds stamp - (q : ℝ) * tickSeconds unit| ≤
        ((Binary64.ulp (Binary64.count stamp unit) / 2 : ℚ) : ℝ) * tickSeconds unit :=
  Proofs.Numeric.UnixInterop.binary64Rne_error encoded

/-- On common physical support, the discrepancy of successful binary64 RNE encodings
    is bounded by the clock discrepancy plus the two normalized half-ULP errors. -/
theorem binary64Rne_discrepancy {a b : Convention} (t : ↑(a.domain ∩ b.domain))
    {sa sb : UnixTime} {ua ub : TickUnit} {pa pb : F64}
    (ga : unixSeconds sa = a.forward ⟨t.val, t.property.1⟩)
    (gb : unixSeconds sb = b.forward ⟨t.val, t.property.2⟩)
    (ea : Binary64.encodeRne sa ua = .ok pa) (eb : Binary64.encodeRne sb ub = .ok pb) :
    ∃ qa qb : ℚ, pa.toRat? = some qa ∧ pb.toRat? = some qb ∧
      |(qa : ℝ) * tickSeconds ua - (qb : ℝ) * tickSeconds ub| ≤
        |a.forward ⟨t.val, t.property.1⟩ - b.forward ⟨t.val, t.property.2⟩| +
          ((Binary64.ulp (Binary64.count sa ua) / 2 : ℚ) : ℝ) * tickSeconds ua +
          ((Binary64.ulp (Binary64.count sb ub) / 2 : ℚ) : ℝ) * tickSeconds ub :=
  Proofs.Numeric.UnixInterop.binary64Rne_discrepancy t ga gb ea eb

end Silmaril.Numeric.UnixInterop
