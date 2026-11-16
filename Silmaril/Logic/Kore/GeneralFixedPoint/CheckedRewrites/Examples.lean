module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Examples

/-- Deliberately malformed freely constructed scope: its symbol returns a sort
which has no declaration. The source module checker would also reject it. -/
def undeclaredScope : Kore.Modules.Scope :=
  ⟨[], [⟨⟨"Malformed", 0⟩, ⟨"c", [], "Missing"⟩⟩], []⟩

def undeclaredRule : RawRewrite :=
  ⟨"Missing", .app "c" [], .top, .app "c" []⟩

/-- Application elaboration alone does not establish declaration validity for
a freely constructed scope, so the rewrite constructor checks the sort explicitly. -/
theorem application_alone_accepts :
    (Predicates.checkValue undeclaredScope [] "Missing" 2 (.app "c" [])).isSome = true := by
  rfl

/-- The operational smart constructor closes that scope-validity gap. -/
theorem undeclared_configuration_rejects :
    checkRewrite undeclaredScope "Missing" 2 undeclaredRule = none := by
  rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Examples
