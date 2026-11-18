module

public import Silmaril.Formats.SExp.Pose2.Defs
public import Silmaril.Formats.SExp.Family.Thms
import Silmaril.Proofs.Formats.SExp.Pose2.Basic

/-!
# POSE as `SExp2`: laws

* every value read from POSE text is recursively proper (`isProper_of_parse?`), so no improper
  value is ever read (`parse?_ne_of_not_proper`): POSE has no dotted pairs;
* `toPose?` is sound for the embedding (`ofPose_toPose?`), so improper values have no POSE text
  (`print?_eq_none_of_not_proper`);
* the checked printer is sound: `print? e = some t → parse? t = some e` (`print?_sound`), and
  `parse?` is `Pose.parse?` followed by the injective embedding (`parse?_eq_some_iff`,
  `ofPose_injective`).
-/

@[expose] public section

namespace Silmaril.Formats.Pose2

theorem ofPose_injective : Function.Injective ofPose := SExp.toSExp2_injective

theorem ofPose_isProper (p : Pose) : SExp2.IsProper (ofPose p) := SExp.toSExp2_proper p

theorem parse?_eq_some_iff {s : String} {e : Pose2} :
    parse? s = some e ↔ ∃ p, Pose.parse? s = some p ∧ ofPose p = e := by
  simp [parse?]

theorem isProper_of_parse? {s : String} {e : Pose2} (h : parse? s = some e) : SExp2.IsProper e := by
  obtain ⟨p, -, rfl⟩ := parse?_eq_some_iff.1 h
  exact ofPose_isProper p

theorem parse?_ne_of_not_proper {e : Pose2} (h : ¬ SExp2.IsProper e) (s : String) :
    parse? s ≠ some e := fun hs => h (isProper_of_parse? hs)

theorem ofPose_toPose? {e : Pose2} {p : Pose} (h : e.toPose? = some p) : ofPose p = e :=
  Silmaril.Proofs.Formats.SExp.Pose2.toPose?_sound h

theorem print?_eq_none_of_not_proper {e : Pose2} (h : ¬ SExp2.IsProper e) : print? e = none := by
  cases hp : e.toPose? with
  | none => simp [print?, hp]
  | some p => exact absurd (ofPose_toPose? hp ▸ ofPose_isProper p) h

/-- **Printer soundness.** -/
theorem print?_sound {e : Pose2} {t : String} (h : print? e = some t) : parse? t = some e := by
  simp only [print?, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, ht⟩ := h
  rw [parse?_eq_some_iff]
  exact ⟨p, Pose.print?_sound ht, ofPose_toPose? hp⟩

end Silmaril.Formats.Pose2
