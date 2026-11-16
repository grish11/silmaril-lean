module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Modules.Thms

-- variant-of: Kore.GeneralFixedPoint.ModuleExamples | style: source aliases | see-also: GeneralFixedPoint.ModuleExamples
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.ModuleExamples

/-- Both namespaces, an alias chain, and genuine μ/ν bodies in a complete
importing source definition. Element-named actuals are arbitrary patterns. -/
def source : String := "[]
module BASE
  sort S{} []
  symbol seed{}():S{} []
  symbol step{}(S{}):S{} []
  alias both{}(S{},S{}):S{} where both{}(E:S{},@P:S{}) := \\and{S{}}(\\mu{}(@X:S{},\\or{S{}}(E:S{},step{}(@X:S{}))),\\nu{}(@Z:S{},\\and{S{}}(@P:S{},\\or{S{}}(E:S{},step{}(@Z:S{}))))) []
  alias chain{}(S{},S{}):S{} where chain{}(E:S{},@P:S{}) := both{}(E:S{},@P:S{}) []
  alias cap{}(S{},S{}):S{} where cap{}(E:S{},@P:S{}) := \\exists{S{}}(x:S{},\\and{S{}}(E:S{},\\mu{}(@X:S{},\\or{S{}}(@P:S{},@X:S{})))) []
endmodule []
module USE
  import BASE []
  axiom{} chain{}(\\or{S{}}(seed{}(),step{}(seed{}())),\\top{S{}}()) []
  claim{} cap{}(x:S{},@X:S{}) []
endmodule []"

theorem checked_source : (Modules.checkText 48 source).isSome = true := by decide +kernel

def checked : Checking.CheckedDefinition := (Modules.checkText 48 source).get checked_source

def base : Checking.CheckedModule checked.ambient := checked.modules.get ⟨0, by decide +kernel⟩
def useModule : Checking.CheckedModule checked.ambient := checked.modules.get ⟨1, by decide +kernel⟩

theorem imported_axiom_count : useModule.axioms.length = 1 := by decide +kernel

def captureRaw : RawPattern := .app "cap" [.evar "x" "S", .svar "@X" "S"]

def captureExpected : Pattern checked.ambient [("@X", "S")] [("x", "S")] "S" :=
  .ex "S" (.conj (.base (.var 1))
    (Matching.GeneralFixedPoint.Pattern.mu
      (P' := Fin.cases "S" (context [("@X", "S")])) (.disj (.setvar 1) (.setvar 0))))

/-- Object and set variables of the actuals remain free across same-named
binders inside the alias body. The compiler performs the native expansion. -/
theorem capture_expansion :
    Checking.elaborate checked.ambient checked.aliases 48 [("@X", "S")] [("x", "S")]
      "S" captureRaw = some captureExpected := by rfl

def seedSymbol : Kore.Modules.NamedSymbol := ⟨⟨"BASE", 1⟩, ⟨"seed", [], "S"⟩⟩
def stepSymbol : Kore.Modules.NamedSymbol := ⟨⟨"BASE", 2⟩, ⟨"step", ["S"], "S"⟩⟩

theorem ambient_symbols : checked.ambient.symbols = [seedSymbol, stepSymbol] := by decide +kernel

def seedDeclaration : {d : Kore.Modules.NamedSymbol // d ∈ checked.ambient.symbols} :=
  ⟨seedSymbol, by decide +kernel⟩

theorem find_seed : checked.ambient.symbols.attach.find?
    (fun d => d.val.declaration.name == "seed") = some seedDeclaration := by decide +kernel

abbrev naturalModel : Matching.GeneralFixedPoint.Model checked.ambient.signature where
  carrier _ := Nat
  nonempty _ := ⟨0⟩
  operation op values :=
    if op.val.declaration.name == "seed" then {0, 1}
    else {result | ∃ i, result = values i + 1}

/-- A concrete actual argument is a two-element set. It cannot be represented
by any singleton element valuation. -/
theorem seed_nonsingleton :
    Semantics.denote checked.ambient checked.aliases naturalModel 48 [] [] "S"
      (.app "seed" []) = some ({0, 1} : Set Nat) := by
  simp [Semantics.denote, find_seed, seedDeclaration, seedSymbol,
    naturalModel, Kore.Modules.Checking.collect]
  ext x
  rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.ModuleExamples
