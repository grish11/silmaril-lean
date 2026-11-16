module

public import Silmaril.Formats.SExp.Pose2.Thms

/-! # POSE as `SExp2`: examples -/

namespace Silmaril.Formats.Pose2

example : (parse? "(a . b)").isNone = true := by cbv
example : (parse? "(foo \"bar\")").isSome = true := by cbv
/-- An improper value has no POSE text. -/
example : print? (.cons (.atom (.symbol "a")) (.atom (.symbol "b"))) = none :=
  print?_eq_none_of_not_proper (by decide)

end Silmaril.Formats.Pose2
