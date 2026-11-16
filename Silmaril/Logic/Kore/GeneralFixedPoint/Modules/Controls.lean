module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Modules.Examples
public import Silmaril.Logic.Kore.GeneralFixedPoint.Hets

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Controls
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A negative self-reference is not made meaningful by the raw sInf fallback. -/
theorem negative_binder_rejected : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\not{S{}}(@X:S{})) []
endmodule []").isNone = true := by decide +kernel

theorem negative_nested_binder_rejected : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\nu{}(@Y:S{},\\or{S{}}(@X:S{},\\not{S{}}(@Y:S{})))) []
endmodule []").isNone = true := by decide +kernel

/-- Implication is contravariant in its antecedent. -/
theorem negative_implication_rejected : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\implies{S{}}(@X:S{},\\bottom{S{}}())) []
endmodule []").isNone = true := by decide +kernel

theorem positive_implication_accepted : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\implies{S{}}(\\bottom{S{}}(),@X:S{})) []
endmodule []").isSome = true := by decide +kernel

/-- General free sets may occur with both signs inside a locally positive body. -/
theorem mixed_free_under_binder_accepted : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\and{S{}}(@X:S{},\\or{S{}}(@Y:S{},\\not{S{}}(@Y:S{})))) []
endmodule []").isSome = true := by decide +kernel

theorem shadowed_negative_binder_rejected : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\nu{}(@X:S{},\\not{S{}}(@X:S{}))) []
endmodule []").isNone = true := by decide +kernel

/-- Negating a complete fixed point is allowed: positivity is local to its body. -/
theorem negated_fixedpoint_accepted : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 axiom{} \\not{S{}}(\\mu{}(@X:S{},@X:S{})) []
endmodule []").isSome = true := by decide +kernel

theorem aliases_still_rejected : (Modules.checkText 32 "[]
module TEST
 sort S{} []
 alias hold{}(S{}):S{} where hold{}(X:S{}):=X:S{} []
endmodule []").isNone = true := by decide +kernel

theorem hidden_symbol_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
 symbol seed{}():S{} []
endmodule []
module USE
 axiom{} \\not{S{}}(seed{}()) []
endmodule []").isNone = true := by decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.Controls
