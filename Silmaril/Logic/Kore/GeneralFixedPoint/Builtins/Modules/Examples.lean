module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Defs

-- variant-of: Kore.GeneralFixedPoint.Aliases.ModuleExamples | style: builtin domain values and hooks | see-also: GeneralFixedPoint.Aliases.ModuleExamples

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.ModuleExamples

/-- Arbitrary module names, imports, declarations and alias bodies are retained.
The alias bodies contain actual domain values and declared hooks. -/
def sourceWith (eqHook eqArgument integerSort integerText booleanText imports : String) : String := "[]
module INTEGER-BOOLEAN
  sort SortInt{} []
  sort SortBool{} []
  hooked-symbol eqInt{}(" ++ eqArgument ++ "{},SortInt{}):SortBool{} [hook{}(\"" ++ eqHook ++ "\")]
  hooked-symbol notBool{}(SortBool{}):SortBool{} [hook{}(\"BOOL.not\")]
  alias isZero{}(SortInt{}):SortBool{} where isZero{}(X:SortInt{}) := eqInt{}(X:SortInt{},\\dv{SortInt{}}(\"0\")) []
  alias isNonzero{}(SortInt{}):SortBool{} where isNonzero{}(X:SortInt{}) := notBool{}(isZero{}(X:SortInt{})) []
  axiom{} \\top{SortBool{}}() []
endmodule []
module CLIENT
" ++ imports ++ "  symbol extra{}():SortInt{} []
  axiom{} \\or{SortBool{}}(isNonzero{}(\\dv{" ++ integerSort ++ "{}}(\"" ++ integerText ++ "\")),\\not{SortBool{}}(isNonzero{}(\\dv{" ++ integerSort ++ "{}}(\"" ++ integerText ++ "\")))) []
  claim{} eqInt{}(\\dv{SortInt{}}(\"0\"),\\dv{SortInt{}}(\"0\")) []
  claim{} notBool{}(\\dv{SortBool{}}(\"" ++ booleanText ++ "\")) []
  claim{} \\dv{SortBool{}}(\"true\") []
endmodule []"

def source : String := sourceWith "INT.eq" "SortInt" "SortInt" "-2" "false"
  "  import INTEGER-BOOLEAN []\n"

theorem checked_source : (Checking.checkText 48 source).isSome = true := by decide +kernel

def checked : Checking.Package := (Checking.checkText 48 source).get checked_source

def client : Checking.CheckedModule checked.checked := checked.modules.get ⟨1, by decide +kernel⟩

theorem import_axioms_retained : client.axioms.length = 2 := by decide +kernel
theorem claims_are_obligations : client.claims.length = 3 := by decide +kernel

/-- Equal zero literals exist in both modules; their declaration identities and
module-specific generated names remain distinct. -/
theorem literal_module_origins : checked.checked.literals.map
    (fun b => (b.symbol.origin.moduleName, b.literal)) =
    [("INTEGER-BOOLEAN", .integer 0), ("CLIENT", .integer (-2)), ("CLIENT", .integer 0),
      ("CLIENT", .boolean false), ("CLIENT", .boolean true)] := by decide +kernel

theorem aliases_keep_defining_module : checked.checked.aliases.map
    (fun a => (a.symbol.name, a.moduleIndex)) = [("isZero", 0), ("isNonzero", 0)] := by
  decide +kernel

def firstOrderSymbols {scope : Kore.Modules.Scope} {k : Nat}
    {Γ : Fin k → String} {s : String} (p : Matching.FirstOrder.Pattern scope.signature Γ s) :
    List Kore.Modules.NamedSymbol := by
  induction p with
  | var _ => exact []
  | app op _ ih => exact op.val :: (List.ofFn ih).flatten
  | neg _ ih => exact ih
  | conj _ _ ih jq => exact ih ++ jq
  | ex _ _ ih => exact ih

def nativeSymbols {scope : Kore.Modules.Scope} {r k : Nat}
    {P : Fin r → String} {Γ : Fin k → String} {s : String}
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P Γ s) : List Kore.Modules.NamedSymbol := by
  induction p with
  | base p => exact firstOrderSymbols p
  | setvar _ => exact []
  | app op _ ih => exact op.val :: (List.ofFn ih).flatten
  | neg _ ih => exact ih
  | conj _ _ ih jq => exact ih ++ jq
  | ex _ _ ih => exact ih
  | mu _ ih => exact ih
  | nu _ ih => exact ih

/-- The caller's zero actual uses CLIENT's literal, while the zero written in
an imported alias body still uses INTEGER-BOOLEAN's literal declaration. -/
theorem imported_alias_literal_namespace :
    (Checking.elaborate checked.checked.native.ambient checked.checked.aliases checked.checked.literals
      checked.checked.literalPrefix 1 48 [] [] "SortBool"
      (.app "isZero" [.domainValue "SortInt" "0"])).map nativeSymbols =
    some [⟨⟨"INTEGER-BOOLEAN", 2⟩, ⟨"eqInt", ["SortInt", "SortInt"], "SortBool"⟩⟩,
      ⟨⟨"CLIENT", 7⟩, literalDeclaration checked.checked.literalPrefix 1 (.integer 0)⟩,
      ⟨⟨"INTEGER-BOOLEAN", 7⟩, literalDeclaration checked.checked.literalPrefix 0 (.integer 0)⟩] := by
  decide +kernel

def wrongHook : String := sourceWith "INT.unknown" "SortInt" "SortInt" "-2" "false" "  import INTEGER-BOOLEAN []\n"
def wrongProfile : String := sourceWith "INT.eq" "SortBool" "SortInt" "-2" "false" "  import INTEGER-BOOLEAN []\n"
def wrongInteger : String := sourceWith "INT.eq" "SortInt" "SortInt" "not-an-integer" "false" "  import INTEGER-BOOLEAN []\n"
def wrongBoolean : String := sourceWith "INT.eq" "SortInt" "SortInt" "-2" "False" "  import INTEGER-BOOLEAN []\n"
def wrongLiteralSort : String := sourceWith "INT.eq" "SortInt" "SortBool" "-2" "false" "  import INTEGER-BOOLEAN []\n"
def missingImport : String := sourceWith "INT.eq" "SortInt" "SortInt" "-2" "false" ""

theorem rejects_wrong_hook : Checking.checkText 48 wrongHook = none := by decide +kernel
theorem rejects_wrong_profile : Checking.checkText 48 wrongProfile = none := by decide +kernel
theorem rejects_wrong_integer : Checking.checkText 48 wrongInteger = none := by decide +kernel
theorem rejects_wrong_boolean : Checking.checkText 48 wrongBoolean = none := by decide +kernel
theorem rejects_wrong_literal_sort : Checking.checkText 48 wrongLiteralSort = none := by decide +kernel
theorem rejects_missing_import : Checking.checkText 48 missingImport = none := by decide +kernel
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.ModuleExamples
