module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Defs


@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Canonical

def equality : Kore.Modules.NamedSymbol := ⟨⟨"BASE", 2⟩, ⟨"eqInt", ["SortInt", "SortInt"], "SortBool"⟩⟩
def negation : Kore.Modules.NamedSymbol := ⟨⟨"BASE", 3⟩, ⟨"notBool", ["SortBool"], "SortBool"⟩⟩
/-- A complete checked source definition with a satisfiable axiom and all four
literal constants used by the concrete model below. -/
def source : String := "[] module BASE
 sort SortInt{} [] sort SortBool{} []
 hooked-symbol eqInt{}(SortInt{},SortInt{}):SortBool{} [hook{}(\"INT.eq\")]
 hooked-symbol notBool{}(SortBool{}):SortBool{} [hook{}(\"BOOL.not\")]
 axiom{} \\top{SortBool{}}() []
 claim{} \\dv{SortInt{}}(\"0\") []
 claim{} \\dv{SortInt{}}(\"-2\") []
 claim{} \\dv{SortBool{}}(\"true\") []
 claim{} \\dv{SortBool{}}(\"false\") []
 endmodule []"

theorem source_parsed : (Syntax.parse source).isSome = true := by decide +kernel

def parsed : Aliases.SourceDefinition := (Syntax.parse source).get source_parsed

def literalPrefix : String := freshPrefix parsed

def zero : LiteralBinding := ⟨⟨⟨"BASE", 9⟩, literalDeclaration literalPrefix 0 (.integer 0)⟩, .integer 0⟩
def negative : LiteralBinding := ⟨⟨⟨"BASE", 10⟩, literalDeclaration literalPrefix 0 (.integer (-2))⟩, .integer (-2)⟩
def truth : LiteralBinding := ⟨⟨⟨"BASE", 11⟩, literalDeclaration literalPrefix 0 (.boolean true)⟩, .boolean true⟩
def falsity : LiteralBinding := ⟨⟨⟨"BASE", 12⟩, literalDeclaration literalPrefix 0 (.boolean false)⟩, .boolean false⟩
def literals : List LiteralBinding := [zero, negative, truth, falsity]
def hooks : List HookBinding := [⟨equality, .intEq⟩, ⟨negation, .boolNot⟩]
def scope : Kore.Modules.Scope := ⟨[(⟨"BASE", 0⟩, "SortInt"), (⟨"BASE", 1⟩, "SortBool")],
  [equality, negation, zero.symbol, negative.symbol, truth.symbol, falsity.symbol], []⟩

def Carrier (s : String) : Type :=
  if s = "SortInt" then Int else if s = "SortBool" then Bool else Unit

def native : Matching.GeneralFixedPoint.Model scope.signature where
  carrier := Carrier
  nonempty s := by unfold Carrier; split <;> (try split) <;> infer_instance
  operation := by
    intro n inputs output op args
    refine {result | ?_}
    rcases op with ⟨symbol, member, profile, out⟩
    simp only [scope, List.mem_cons, List.not_mem_nil, or_false] at member
    refine if h0 : symbol = equality then ?_ else
      if h1 : symbol = negation then ?_ else
      if h2 : symbol = zero.symbol then ?_ else
      if h3 : symbol = negative.symbol then ?_ else
      if h4 : symbol = truth.symbol then ?_ else ?_
    all_goals try subst symbol
    · have hn : n = 2 := by simpa [equality] using (congrArg List.length profile).symm
      subst n
      have h0 : inputs 0 = "SortInt" := (List.cons.inj profile).1.symm
      have h1 : inputs 1 = "SortInt" := (List.cons.inj (List.cons.inj profile).2).1.symm
      simp only [equality] at out
      subst output
      exact result = Operational.Conditional.intEqual (cast (congrArg Carrier h0) (args 0)) (cast (congrArg Carrier h1) (args 1))
    · have hn : n = 1 := by simpa [negation] using (congrArg List.length profile).symm
      subst n
      have h0 : inputs 0 = "SortBool" := (List.cons.inj profile).1.symm
      simp only [negation] at out
      subst output
      exact result = !(cast (congrArg Carrier h0) (args 0))
    all_goals
      try
        have last : symbol = falsity.symbol := by simpa [h0, h1, h2, h3, h4] using member
        subst symbol
      have hn : n = 0 := by
        simpa [zero, negative, truth, falsity, literalDeclaration] using (congrArg List.length profile).symm
      subst n
    · simp only [zero, literalDeclaration, Literal.sort] at out
      subst output
      exact result = (0 : Int)
    · simp only [negative, literalDeclaration, Literal.sort] at out
      subst output
      exact result = (-2 : Int)
    · simp only [truth, literalDeclaration, Literal.sort] at out
      subst output
      exact result = true
    · simp only [falsity, literalDeclaration, Literal.sort] at out
      subst output
      exact result = false

def carriers : Carriers native := ⟨Equiv.refl Int, Equiv.refl Bool⟩

theorem laws : Laws native literalPrefix literals hooks carriers := by
  constructor
  · intro b member l value op identity
    simp only [literals, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      subst l
      rcases op with ⟨symbol, member, profile, out⟩
      dsimp only at identity
      subst symbol
      ext x
      simp [native, carriers, Carriers.literal, zero, negative, truth, falsity,
        equality, negation, literalDeclaration, Literal.sort]
      rfl
  · intro b member which op identity args
    simp only [hooks, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rcases op with ⟨symbol, member, profile, out⟩
      dsimp only at identity
      subst symbol
      ext x
      simp [native, carriers, equality, negation, zero, negative, truth, falsity,
        literalDeclaration, Literal.sort]
      rfl
    · contradiction
  · intro b member which op identity args
    simp only [hooks, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · contradiction
    · rcases op with ⟨symbol, member, profile, out⟩
      dsimp only at identity
      subst symbol
      ext x
      simp [native, carriers, equality, negation, zero, negative, truth, falsity,
        literalDeclaration, Literal.sort]
      rfl

def model : Model scope literalPrefix literals hooks := ⟨native, carriers, laws⟩

theorem builtin_models_nonempty : Nonempty (Model scope literalPrefix literals hooks) := ⟨model⟩
def equalityOp : scope.signature.operations 2 (fun _ => "SortInt") "SortBool" :=
  ⟨equality, by decide +kernel, rfl, rfl⟩

def negationOp : scope.signature.operations 1 (fun _ => "SortBool") "SortBool" :=
  ⟨negation, by decide +kernel, rfl, rfl⟩

theorem zero_guard : native.operation equalityOp (fun _ => (0 : Int)) = {true} := by
  simpa [carriers, Equiv.refl, Operational.Conditional.intEqual] using
    laws.intEq ⟨equality, .intEq⟩ (by simp [hooks]) rfl equalityOp rfl (fun _ => (0 : Int))

theorem negative_zero_guard : native.operation equalityOp (fun i : Fin 2 => if i.val = 0 then (-2 : Int) else (0 : Int)) = {false} := by
  simpa [carriers, Equiv.refl, Operational.Conditional.intEqual] using
    laws.intEq ⟨equality, .intEq⟩ (by simp [hooks]) rfl equalityOp rfl (fun i : Fin 2 => if i.val = 0 then (-2 : Int) else (0 : Int))

theorem negative_nonzero_guard : native.operation negationOp (fun _ => false) = {true} := by
  simpa [carriers, Equiv.refl] using
    laws.boolNot ⟨negation, .boolNot⟩ (by simp [hooks]) rfl negationOp rfl (fun _ => false)

theorem zero_nonzero_guard : native.operation negationOp (fun _ => true) = {false} := by
  simpa [carriers, Equiv.refl] using
    laws.boolNot ⟨negation, .boolNot⟩ (by simp [hooks]) rfl negationOp rfl (fun _ => true)

theorem negative_source_literal :
    Semantics.denote scope [] native carriers 2 [] [] "SortInt" (.domainValue "SortInt" "-2") =
      some {( -2 : Int)} := by rfl

theorem zero_source_literal :
    Semantics.denote scope [] native carriers 2 [] [] "SortInt" (.domainValue "SortInt" "0") =
      some {(0 : Int)} := by rfl

theorem source_checked : (Checking.checkText 24 source).isSome = true := by decide +kernel

def checked : Checking.Package := (Checking.checkText 24 source).get source_checked

theorem checked_scope : checked.checked.native.ambient = scope := by
  have ext (a b : Kore.Modules.Scope) (hs : a.sorts = b.sorts)
      (ho : a.symbols = b.symbols) (ha : a.aliases = b.aliases) : a = b := by
    cases a
    cases b
    simp_all
  apply ext
  · decide +kernel
  · decide +kernel
  · have empty : checked.checked.native.ambient.aliases.length = 0 := by decide +kernel
    exact List.length_eq_zero_iff.mp empty

theorem checked_prefix : checked.checked.literalPrefix = literalPrefix := by decide +kernel

theorem checked_literals : checked.checked.literals = literals := by decide +kernel

theorem checked_hooks : checked.checked.hooks = hooks := by decide +kernel

/-- An actual model of the successfully checked source signature and its finite
literal/hook bindings, not merely a hypothetical unrestricted interpretation. -/
def checkedModel : Model checked.checked.native.ambient checked.checked.literalPrefix
    checked.checked.literals checked.checked.hooks := by
  rw [checked_scope, checked_prefix, checked_literals, checked_hooks]
  exact model

def baseModule : Checking.CheckedModule checked.checked :=
  checked.modules.get ⟨0, by decide +kernel⟩

def firstAxiom : LocatedSentence checked.checked.native.ambient checked.checked.literals
    checked.checked.literalPrefix := baseModule.localAxioms.get ⟨0, by decide +kernel⟩

theorem axioms_singleton : baseModule.axioms = [firstAxiom] := by
  have count : baseModule.localAxioms.length = 1 := by decide +kernel
  have inherited : baseModule.inheritedAxioms.length = 0 := by decide +kernel
  have one {α : Type} (xs : List α) (h : xs.length = 1) :
      xs = [xs.get ⟨0, by omega⟩] := by
    cases xs with
    | nil => simp at h
    | cons a tail =>
      have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst tail
      rfl
  simp only [Checking.CheckedModule.axioms, List.length_eq_zero_iff.mp inherited,
    List.append_nil, firstAxiom]
  exact one _ count

theorem source_axioms_satisfied : ∀ p ∈ baseModule.axiomSet, p.Satisfies checkedModel := by
  intro p hp
  obtain ⟨item, member, same⟩ := hp
  rw [axioms_singleton] at member
  simp only [List.mem_singleton] at member
  subst item
  subst p
  apply CheckedSentence.top_satisfies
  have test : (match firstAxiom.source.raw with
    | .top actual => actual == firstAxiom.source.sort
    | _ => false) = true := by decide +kernel
  cases raw : firstAxiom.source.raw <;> simp_all

theorem source_theory_satisfiable :
    ∃ M : Model checked.checked.native.ambient checked.checked.literalPrefix
      checked.checked.literals checked.checked.hooks, ∀ p ∈ baseModule.axiomSet, p.Satisfies M :=
  ⟨checkedModel, source_axioms_satisfied⟩

theorem native_theory_satisfiable :
    ∃ M : Model checked.checked.native.ambient checked.checked.literalPrefix
      checked.checked.literals checked.checked.hooks,
      ∀ p ∈ baseModule.nativeAxiomSet, Matching.GeneralFixedPoint.Sentence.Satisfies M.native p :=
  baseModule.satisfiable_native_iff.mp source_theory_satisfiable

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Canonical
