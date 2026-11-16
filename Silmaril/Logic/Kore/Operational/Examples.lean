module

public import Silmaril.Logic.Kore.Operational.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Examples

/-- Exact captured names in the pinned emitted TEST.CD axiom and rule2LHS alias. -/
def sourceContext : Context := ⟨"Var'Unds'DotVar1", "Var'Unds'DotVar0"⟩
def sourceAlias : Alias := ⟨"rule2LHS", configTree sourceContext ⟨"c"⟩⟩
def cd : Rule := ⟨⟨"c"⟩, ⟨"d"⟩⟩

/-- Parsed operational body and resolved alias, retaining checked metadata.
The full emitted module is not imported or claimed supported. -/
def sourceDeclaration : Declaration :=
  ⟨.ruleAxiom, [], .rewrites "SortGeneratedTopCell"
    (aliasApplication sourceContext sourceAlias) (configTree sourceContext cd.after), [
      .app1 "label" [] (.stringLiteral "TEST.CD"),
      .app1 "org'Stop'kframework'Stop'attributes'Stop'Source" []
        (.stringLiteral "Source(/home/jost/work/RV/code/haskell-backend/test/rpc-server/resources/a-to-f/test.k)"),
      .app1 "org'Stop'kframework'Stop'definition'Stop'Production" []
        (.stringLiteral "syntax #RuleContent ::= #RuleBody [klabel(#ruleNoConditions), symbol]"),
      .app1 "org'Stop'kframework'Stop'attributes'Stop'Location" []
        (.stringLiteral "Location(14,14,14,20)"),
      .app1 "UNIQUE'Unds'ID" []
        (.stringLiteral "ff014a1391cb03a765bde1287d17bf3bcf43de53891ef00eb786fba0821482f3")]⟩

/-- Exact archived axiom bytes with whitespace removed only outside strings.
The source receipt identifies the original span and normalization. -/
def archivedAxiom : String := "axiom{}\\rewrites{SortGeneratedTopCell{}}(rule2LHS{}(Var'Unds'DotVar0:SortGeneratedCounterCell{},Var'Unds'DotVar1:SortK{}),\\and{SortGeneratedTopCell{}}(\\top{SortGeneratedTopCell{}}(),Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{},SortKItem{}}(\\dv{SortState{}}(\"d\")),Var'Unds'DotVar1:SortK{})),Var'Unds'DotVar0:SortGeneratedCounterCell{})))[label{}(\"TEST.CD\"),org'Stop'kframework'Stop'attributes'Stop'Source{}(\"Source(/home/jost/work/RV/code/haskell-backend/test/rpc-server/resources/a-to-f/test.k)\"),org'Stop'kframework'Stop'definition'Stop'Production{}(\"syntax #RuleContent ::= #RuleBody [klabel(#ruleNoConditions), symbol]\"),org'Stop'kframework'Stop'attributes'Stop'Location{}(\"Location(14,14,14,20)\"),UNIQUE'Unds'ID{}(\"ff014a1391cb03a765bde1287d17bf3bcf43de53891ef00eb786fba0821482f3\")]"

def archivedAlias : String := "aliasrule2LHS{}(SortGeneratedCounterCell{},SortK{}):SortGeneratedTopCell{}whererule2LHS{}(Var'Unds'DotVar0:SortGeneratedCounterCell{},Var'Unds'DotVar1:SortK{}):=\\and{SortGeneratedTopCell{}}(\\top{SortGeneratedTopCell{}}(),Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{},SortKItem{}}(\\dv{SortState{}}(\"c\")),Var'Unds'DotVar1:SortK{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}))[]"

set_option maxRecDepth 10000 in
theorem alias_tree_correspondence : sourceAlias.render sourceContext = archivedAlias.toList := by decide

set_option maxRecDepth 10000 in
theorem source_tree_correspondence : sourceDeclaration.render = archivedAxiom.toList := by decide

theorem source_elaborates :
    transitionRule sourceContext sourceAlias sourceDeclaration = some cd := by decide

theorem claim_elaborates_as_goal : elaborateRule sourceContext sourceAlias
    {sourceDeclaration with kind := .claim} = some cd := by decide

theorem claim_adds_no_edge : transitionRule sourceContext sourceAlias
    {sourceDeclaration with kind := .claim} = none := rfl

/-- Unknown semantic attributes, parametric declarations and unsupported next
claims cannot silently become source rewrite rules. -/
theorem rejects_attribute : transitionRule sourceContext sourceAlias
    {sourceDeclaration with attributes := [.unsupported "priority"]} = none := by decide

theorem rejects_sort_parameter : transitionRule sourceContext sourceAlias
    {sourceDeclaration with sortVariables := ["S"]} = none := by decide

theorem rejects_next : transitionRule sourceContext sourceAlias
    {sourceDeclaration with body := .next "SortGeneratedTopCell" sourceAlias.body} = none := by decide

theorem rejects_wrong_sort : transitionRule sourceContext sourceAlias
    {sourceDeclaration with body := (.rewrites "SortK" sourceAlias.body
      (configTree sourceContext cd.after))} = none := by decide

theorem rejects_changed_capture : elaborateConfig sourceContext
    (configTree ⟨"OtherTail", sourceContext.counter⟩ cd.after) = none := by decide

theorem rejects_reversed_alias_arguments : elaborateLeft sourceContext sourceAlias
    (.app2 sourceAlias.name [] (.variable sourceContext.tail "SortK")
      (.variable sourceContext.counter "SortGeneratedCounterCell")) = none := by decide

theorem checked_source_input : checkInput sourceContext sourceAlias
    [sourceDeclaration, {sourceDeclaration with kind := .claim}] = some ⟨[cd], [cd]⟩ := by decide

theorem rejects_entire_bad_input : checkInput sourceContext sourceAlias
    [sourceDeclaration, {sourceDeclaration with body := .unsupported "hook"}] = none := by decide

/-- Independent executable source step on all K tails and counter values. -/
def sourceStep (x y : Config) : Prop :=
  ∃ tail count, x = ⟨"c" :: tail, count⟩ ∧ y = ⟨"d" :: tail, count⟩

theorem source_step_exact (x y : Config) : Step [cd] x y ↔ sourceStep x y := by
  constructor
  · intro h
    cases h with
    | rule r hr v =>
      have he : r = cd := by simpa only [List.mem_singleton] using hr
      subst r
      exact ⟨v.tail, v.counter, rfl, rfl⟩
  · rintro ⟨tail, count, rfl, rfl⟩
    exact .rule cd (by simp) ⟨tail, count⟩

theorem emitted_rule_valid : cd.Holds sourceStep := by
  apply (rule_holds_iff _ _).mpr
  intro v
  exact ⟨v.tail, v.counter, rfl, rfl⟩

theorem emitted_compiled_valid : cd.compile.Satisfies KSort.config (model sourceStep) := by
  apply (compile_satisfies_iff _ _).mpr
  intro v
  exact .next trivial ⟨v.tail, v.counter, rfl, rfl⟩ (.now rfl)

theorem emitted_matching_valid : Matching.FixedPoint.Sentence.Satisfies (model sourceStep)
    (Reachability.encode KSort.config cd.compile) :=
  (Reachability.encode_correct _ _).mpr emitted_compiled_valid

/-- Counter preservation and actual K tail preservation are semantic facts,
not a dropped-field abstraction. -/
theorem preserves_frame {x y : Config} (h : sourceStep x y) :
    x.counter = y.counter ∧ x.code.tail = y.code.tail := by
  rcases h with ⟨tail, count, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem no_wrong_endpoint : ¬ sourceStep ⟨["c"], 0⟩ ⟨["e"], 0⟩ := by
  rintro ⟨tail, count, hx, hy⟩
  have h := congrArg (fun c : Config => c.code.head?) hy
  simp at h

/-- A claim-only input has no generated transition, so claims cannot prove
execution merely by being listed. -/
theorem no_step_without_axioms (x y : Config) : ¬ Step [] x y := by
  intro h
  cases h with
  | rule r hr _ => simp at hr

end Silmaril.Logic.Kore.Operational.Examples
