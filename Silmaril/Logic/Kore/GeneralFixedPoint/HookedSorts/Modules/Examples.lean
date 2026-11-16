module

public import Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.Modules.Defs

@[expose] public section
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.Examples

/-- Constructed complete definitions, not extracted upstream subtrees. -/
def sourceWith (intName boolName sortHook eqHook eqArgument literalSort integerText imports : String) : String := "[]
module DOMAINS
 hooked-sort " ++ intName ++ "{} [hook{}(\"" ++ sortHook ++ "\")]
 hooked-sort " ++ boolName ++ "{} [hook{}(\"BOOL.Bool\")]
 hooked-symbol eq{}(" ++ eqArgument ++ "{}," ++ intName ++ "{}):" ++ boolName ++ "{} [hook{}(\"" ++ eqHook ++ "\")]
 hooked-symbol not{}(" ++ boolName ++ "{}):" ++ boolName ++ "{} [hook{}(\"BOOL.not\")]
 alias isZero{}(" ++ intName ++ "{}):" ++ boolName ++ "{} where isZero{}(X:" ++ intName ++ "{}) := eq{}(X:" ++ intName ++ "{},\\dv{" ++ intName ++ "{}}(\"0\")) []
 alias isNonzero{}(" ++ intName ++ "{}):" ++ boolName ++ "{} where isNonzero{}(X:" ++ intName ++ "{}) := not{}(isZero{}(X:" ++ intName ++ "{})) []
 axiom{} \\top{" ++ boolName ++ "{}}() []
endmodule []
module CLIENT
" ++ imports ++ "
 symbol extra{}():" ++ intName ++ "{} []
 axiom{} \\or{" ++ boolName ++ "{}}(isNonzero{}(\\dv{" ++ literalSort ++ "{}}(\"" ++ integerText ++ "\")),\\not{" ++ boolName ++ "{}}(isNonzero{}(\\dv{" ++ literalSort ++ "{}}(\"" ++ integerText ++ "\")))) []
 claim{} isZero{}(\\dv{" ++ intName ++ "{}}(\"0\")) []
 claim{} not{}(\\dv{" ++ boolName ++ "{}}(\"false\")) []
endmodule []"

def source : String := sourceWith "Number" "Truth" "INT.Int" "INT.eq" "Number" "Number" "-2" " import DOMAINS []"

theorem accepted : (checkText 48 source).isSome = true := by decide +kernel

def checked : Package := (checkText 48 source).get accepted

theorem selected_integer : checked.bindings.intSort = "Number" := by decide +kernel

theorem selected_boolean : checked.bindings.boolSort = "Truth" := by decide +kernel

theorem retained_origins :
    (sortBindings checked.source).map (fun bs => bs.map (fun b => (b.origin.moduleName, b.origin.declarationIndex, b.name))) =
      some [("DOMAINS", 0, "Number"), ("DOMAINS", 1, "Truth")] := by decide +kernel

theorem imported_axioms_retained :
    letI := checked.bindings
    (checked.checked.modules.map fun m => (m.localAxioms.length, m.inheritedAxioms.length, m.claims.length)) =
      [(1, 0, 0), (1, 1, 2)] := by decide +kernel

/-- Conventional names may even exchange roles: metadata determines meaning. -/
theorem swapped_conventions :
    (checkText 48 (sourceWith "SortBool" "SortInt" "INT.Int" "INT.eq" "SortBool" "SortBool" "-2" " import DOMAINS []")).isSome = true := by decide +kernel

theorem rejects_unknown_sort_hook :
    (checkText 48 (sourceWith "Number" "Truth" "INT.Unknown" "INT.eq" "Number" "Number" "-2" " import DOMAINS []")).isNone = true := by decide +kernel

theorem rejects_unknown_symbol_hook :
    (checkText 48 (sourceWith "Number" "Truth" "INT.Int" "INT.ge" "Number" "Number" "-2" " import DOMAINS []")).isNone = true := by decide +kernel

theorem rejects_wrong_profile :
    (checkText 48 (sourceWith "Number" "Truth" "INT.Int" "INT.eq" "Truth" "Number" "-2" " import DOMAINS []")).isNone = true := by decide +kernel

theorem rejects_bad_literal :
    (checkText 48 (sourceWith "Number" "Truth" "INT.Int" "INT.eq" "Number" "Number" "2.0" " import DOMAINS []")).isNone = true := by decide +kernel

theorem rejects_conventional_literal_sort :
    (checkText 48 (sourceWith "Number" "Truth" "INT.Int" "INT.eq" "Number" "SortInt" "-2" " import DOMAINS []")).isNone = true := by decide +kernel

theorem rejects_missing_import :
    (checkText 48 (sourceWith "Number" "Truth" "INT.Int" "INT.eq" "Number" "Number" "-2" "")).isNone = true := by decide +kernel

theorem rejects_equal_sort_names :
    (checkText 16 "[] module M hooked-sort X{} [hook{}(\"INT.Int\")] hooked-sort X{} [hook{}(\"BOOL.Bool\")] endmodule []").isNone = true := by decide +kernel

theorem rejects_duplicate_hook_declarations :
    (checkText 16 "[] module M hooked-sort X{} [hook{}(\"INT.Int\")] hooked-sort Y{} [hook{}(\"INT.Int\")] hooked-sort B{} [hook{}(\"BOOL.Bool\")] endmodule []").isNone = true := by decide +kernel

theorem rejects_undeclared_bindings :
    (checkText 16 "[] module M sort SortInt{} [] sort SortBool{} [] endmodule []").isNone = true := by decide +kernel

theorem legacy_rejects_hooked_sort :
    (Builtins.Syntax.parse source).isNone = true ∧
      (Aliases.Modules.parse source).isNone = true := by decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.Examples
