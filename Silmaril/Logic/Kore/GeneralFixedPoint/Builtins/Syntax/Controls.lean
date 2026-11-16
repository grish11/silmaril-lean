module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Defs

@[expose] public section
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SyntaxControls
theorem reads_negative : (Literal.parse "SortInt" "-2").isSome = true := by decide +kernel
theorem parses_ordinary : (Syntax.parse "[] module M sort SortInt{} [] endmodule []").isSome = true := by decide +kernel
theorem checks_ordinary_lowering : (checkText 8 "[] module M sort SortInt{} [] endmodule []").isSome = true := by decide +kernel
theorem checks_ordinary_package : (Checking.checkText 8 "[] module M sort SortInt{} [] endmodule []").isSome = true := by decide +kernel
theorem parses_declared_hook : (Syntax.parse "[] module M sort SortInt{} [] sort SortBool{} [] hooked-symbol eq{}(SortInt{},SortInt{}):SortBool{} [hook{}(\"INT.eq\")] endmodule []").isSome = true := by decide +kernel
theorem parses_domain_value : (Syntax.parse "[] module M sort SortInt{} [] axiom{} \\dv{SortInt{}}(\"-2\") [] endmodule []").isSome = true := by decide +kernel
theorem reads_zero : Literal.parse "SortInt" "0" = some (.integer 0) := by decide +kernel

theorem reads_negative_exact : Literal.parse "SortInt" "-2" = some (.integer (-2)) := by decide +kernel

theorem decimal_print : decimalPrint 12345 = "12345" := by decide +kernel

theorem rejects_decimal_lexical_forms :
    ["", "-", "+2", "1_0", " 2", "2.0"].all (fun s => (decimalInteger s).isNone) = true := by
  decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SyntaxControls
