module

import Silmaril.Languages.Python.Source.Scope.Thms
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python.Source

private def inspect (body : List Stmt) (path : BlockPath) (name : Name) : Option Access :=
  (analyze ⟨body⟩).toOption.bind fun tree => (tree.atPath path).bind (·.access name)

private def closedOverLaterBinding : List Stmt :=
  [.functionDef "outer" [] [
    .functionDef "middle" [] [
      .functionDef "inner" [] [.return_ (some (.name "x"))]],
    .assign "x" (.integer 1)]]

#guard inspect closedOverLaterBinding [0, 0, 0] "x" == some (.free [0])
#guard inspect closedOverLaterBinding [0] "x" == some .local
#guard ((analyze ⟨closedOverLaterBinding⟩).toOption.bind (·.atPath [0])).map (·.cells) ==
  some ["x"]
#guard ((analyze ⟨closedOverLaterBinding⟩).toOption.bind (·.atPath [0, 0])).map (·.captures) ==
  some [⟨"x", [0]⟩]

private def shadowedBinding : List Stmt :=
  [.functionDef "outer" [{ name := "x" }] [
    .functionDef "middle" [{ name := "x" }] [
      .functionDef "inner" [] [.nonlocalDecl ["x"], .assign "x" (.integer 2)]]]]

#guard inspect shadowedBinding [0, 0, 0] "x" == some (.free [0, 0])
#guard ((analyze ⟨shadowedBinding⟩).toOption.bind (·.atPath [0])).map (·.cells) == some []
#guard ((analyze ⟨shadowedBinding⟩).toOption.bind (·.atPath [0, 0])).map (·.cells) == some ["x"]

private def barriers : List Stmt :=
  [.assign "m" (.integer 0), .functionDef "outer" [{ name := "x" }] [
    .functionDef "middle" [] [
      .globalDecl ["x"],
      .functionDef "inner" [] [
        .expression (.name "x"), .expression (.name "m")]]]]

#guard inspect barriers [] "m" == some .moduleName
#guard inspect barriers [0, 0] "x" == some .declaredGlobal
#guard inspect barriers [0, 0, 0] "x" == some .implicitGlobal
#guard inspect barriers [0, 0, 0] "m" == some .implicitGlobal

private def defaultsAndControl : List Stmt :=
  [.functionDef "outer" [] [
    .if_ (.name "guard")
      [.functionDef "left" [{ name := "p", defaultValue := some (.call (.name "make") [.name "x"]) }]
        [.return_ (some (.name "p"))]]
      [.functionDef "right" [] [.pass]],
    .while_ (.boolean false) [.delete "x"] [.pass]]]

#guard inspect defaultsAndControl [0] "x" == some .local
#guard inspect defaultsAndControl [0] "make" == some .implicitGlobal
#guard inspect defaultsAndControl [0, 0] "p" == some .local
#guard inspect defaultsAndControl [0, 0] "make" == none
#guard ((analyze ⟨defaultsAndControl⟩).toOption.bind (·.atPath [0, 1])).map (·.context.path) ==
  some [0, 1]
#guard ((analyze ⟨defaultsAndControl⟩).toOption.bind (·.atPath [0, 2])).isNone

private def diagnose (body : List Stmt) : Option Diagnostic :=
  match analyze ⟨body⟩ with
  | .error diagnostic => some diagnostic
  | .ok _ => none

#guard diagnose [.nonlocalDecl ["x"]] == some ⟨[], .nonlocalInModule "x"⟩
#guard diagnose [.assign "x" (.integer 1), .functionDef "f" [] [.nonlocalDecl ["x"]]] ==
  some ⟨[0], .unboundNonlocal "x"⟩
#guard diagnose [.functionDef "f" [{ name := "x" }, { name := "x" }] []] ==
  some ⟨[0], .duplicateParameter "x"⟩
#guard diagnose [.functionDef "f" [{ name := "x" }] [.globalDecl ["x"]]] ==
  some ⟨[0], .parameterDirective "x" .global_⟩
#guard diagnose [.functionDef "f" [] [.globalDecl ["x"], .nonlocalDecl ["x"]]] ==
  some ⟨[0], .conflictingDirectives "x"⟩
#guard diagnose [.functionDef "f" [] [.expression (.name "x"), .globalDecl ["x"]]] ==
  some ⟨[0], .readBeforeDirective "x" .global_⟩
#guard diagnose [.functionDef "f" [] [.delete "x", .globalDecl ["x"]]] ==
  some ⟨[0], .boundBeforeDirective "x" .global_⟩
#guard diagnose [.functionDef "f" [] [.globalDecl ["x"], .globalDecl ["x"]]] == none
#guard diagnose [.functionDef "outer" [{ name := "x" }] [
  .functionDef "middle" [] [
    .globalDecl ["x"], .functionDef "inner" [] [.nonlocalDecl ["x"]]]]] ==
  some ⟨[0, 0, 0], .unboundNonlocal "x"⟩

private def classScopes : List Stmt :=
  [.functionDef "outer" [{ name := "x" }, { name := "y" }, { name := "z" }] [
    .classDef "C" [.name "base"] [
      .globalDecl ["y"],
      .assign "x" (.integer 0),
      .expression (.name "z"),
      .expression (.name "unbound"),
      .functionDef "method" [{ name := "self" }] [
        .expression (.name "x"), .expression (.name "y"),
        .return_ (some (.call (.name "super") []))],
      .classDef "Nested" [] [
        .expression (.name "__class__"),
        .functionDef "owner" [{ name := "self" }] [.return_ (some (.name "__class__"))]]]]]

#guard inspect classScopes [0] "base" == some .implicitGlobal
#guard inspect classScopes [0, 0] "base" == none
#guard inspect classScopes [0, 0] "x" == some .className
#guard inspect classScopes [0, 0] "y" == some .declaredGlobal
#guard inspect classScopes [0, 0] "z" == some (.classFree [0])
#guard inspect classScopes [0, 0] "unbound" == some .className
#guard inspect classScopes [0, 0, 0] "x" == some (.free [0])
#guard inspect classScopes [0, 0, 0] "y" == some (.free [0])
#guard inspect classScopes [0, 0, 0] "__class__" == some (.free [0, 0])
#guard inspect classScopes [0, 0, 1] "__class__" == some (.classFree [0, 0])
#guard inspect classScopes [0, 0, 1, 0] "__class__" == some (.free [0, 0, 1])
#guard ((analyze ⟨classScopes⟩).toOption.bind (·.atPath [0, 0])).map (·.cells) ==
  some ["__class__"]

private def classNonlocal : List Stmt :=
  [.functionDef "outer" [{ name := "x" }] [
    .classDef "C" [] [.nonlocalDecl ["x"], .assign "x" (.integer 2)]]]

#guard inspect classNonlocal [0, 0] "x" == some (.classFree [0])
#guard diagnose [.classDef "C" [] [.nonlocalDecl ["missing"]]] ==
  some ⟨[0], .unboundNonlocal "missing"⟩

private def unresolvedClassNonlocal : List Stmt :=
  [.classDef "Outer" [] [
    .assign "member" (.integer 1),
    .classDef "Inner" [] [.nonlocalDecl ["member"], .expression (.name "member")]]]

#guard diagnose unresolvedClassNonlocal == some ⟨[0, 0], .unboundNonlocal "member"⟩
#guard ((analyze ⟨unresolvedClassNonlocal⟩ .eager .globalFallback).toOption.bind (·.atPath [0, 0])).bind
  (·.access "member") == some .implicitGlobal
#guard ((analyze ⟨classNonlocal⟩ .eager .globalFallback).toOption.bind (·.atPath [0, 0])).bind
  (·.access "x") == some (.classFree [0])

private def lambdaScopes : List Stmt :=
  [.functionDef "outer" [{ name := "x" }, { name := "y" }] [
    .functionDef "f" [{ name := "p", defaultValue := some (.lambda [] (.name "x")) }] [
      .return_ (some
        (.lambda [{ name := "q", defaultValue := some (.name "p") }] (.binary .add (.name "q") (.name "p"))))]
      [.lambda [] (.name "y")]]]

#guard inspect lambdaScopes [0, 0] "x" == some (.free [0])
#guard inspect lambdaScopes [0, 1] "y" == some (.free [0])
#guard inspect lambdaScopes [0, 2] "p" == some .local
#guard inspect lambdaScopes [0, 2, 0] "p" == some (.free [0, 2])
#guard inspect lambdaScopes [0, 2, 0] "q" == some .local
#guard inspect lambdaScopes [0] "<lambda>" == none
#guard ((analyze ⟨lambdaScopes⟩).toOption.bind (·.atPath [0, 2])).map (·.cells) ==
  some ["p"]
#guard diagnose [.expression (.lambda [{ name := "x" }, { name := "x" }] (.name "x"))] ==
  some ⟨[0], .duplicateParameter "x"⟩

private def classHeaderScopes : List Stmt :=
  [.classDef "C" [.lambda [] (.name "baseName")] [.pass] [.lambda [] (.name "decoratorName")]]

#guard inspect classHeaderScopes [0] "decoratorName" == some .implicitGlobal
#guard inspect classHeaderScopes [1] "baseName" == some .implicitGlobal
#guard ((analyze ⟨classHeaderScopes⟩).toOption.bind (·.atPath [2])).map (·.context.kind) ==
  some .class_

private def statementScopes : List Stmt :=
  [.functionDef "f" [] [
    .importFrom ["pkg"] 1 [⟨"member", some "alias"⟩, ⟨"other", none⟩],
    .for_ (.tuple [.name "value", .attribute (.name "receiver") "field"]) (.name "entries")
      [.assignTargets [.list_ [.name "left", .name "right"]] (.name "value")]
      [.deleteTargets [.subscript (.name "mapping") (.name "index")]],
    .try_ [.assert_ (.name "left") (some (.name "message"))]
      [⟨some (.name "Error"), some "caught",
          [.functionDef "inner" [] [.return_ (some (.name "caught"))]]⟩]
      [.expression (.attribute (.name "alias") "field")]
      [.raise_ (some (.name "other")) (some (.name "reason"))]]]

#guard inspect statementScopes [0] "alias" == some .local
#guard inspect statementScopes [0] "member" == none
#guard inspect statementScopes [0] "other" == some .local
#guard inspect statementScopes [0] "receiver" == some .implicitGlobal
#guard inspect statementScopes [0] "field" == none
#guard inspect statementScopes [0] "value" == some .local
#guard inspect statementScopes [0] "left" == some .local
#guard inspect statementScopes [0] "right" == some .local
#guard inspect statementScopes [0] "index" == some .implicitGlobal
#guard inspect statementScopes [0] "reason" == some .implicitGlobal
#guard inspect statementScopes [0, 0] "caught" == some (.free [0])
#guard ((analyze ⟨statementScopes⟩).toOption.bind (·.atPath [0])).map (·.cells) ==
  some ["caught"]
#guard diagnose [.functionDef "f" [] [
  .importFrom ["pkg"] 0 [⟨"member", some "alias"⟩], .globalDecl ["alias"]]] ==
  some ⟨[0], .boundBeforeDirective "alias" .global_⟩
#guard diagnose [.importFrom ["pkg"] 0 [⟨"*", none⟩]] == some ⟨[], .starImport⟩

private def expressionScopes : List Stmt :=
  [.functionDef "f" [] [
    .expression (.dictionary [
      (some (.lambda [] (.name "keyOne")), .lambda [] (.name "valueOne")),
      (some (.lambda [] (.name "keyTwo")), .lambda [] (.name "valueTwo"))]),
    .expression (.callWith (.name "callee") [
      (.keyword "label", .unary .negative (.name "arg")),
      (.unpackIterable, .slice (.name "array") (some (.name "lo")) none (some (.name "stride"))),
      (.unpackMapping, .name "opts")]),
    .expression (.yield_ (some (.conditional
      (.booleanOp .and_ [.name "cond", .comparison (.name "lo") [(.lt, .name "hi")]])
      (.list_ [.floatBits 0, .name "yes"])
      (.tuple [.text [0, 0xd800], .ellipsis, .name "no"]))))]]

#guard inspect expressionScopes [0, 0] "keyOne" == some .implicitGlobal
#guard inspect expressionScopes [0, 1] "keyTwo" == some .implicitGlobal
#guard inspect expressionScopes [0, 2] "valueOne" == some .implicitGlobal
#guard inspect expressionScopes [0, 3] "valueTwo" == some .implicitGlobal
#guard inspect expressionScopes [0] "label" == none
#guard ["callee", "arg", "array", "lo", "stride", "opts", "cond", "hi", "yes", "no"].all
  (fun name => inspect expressionScopes [0] name == some .implicitGlobal)
#guard diagnose [.assign "x" (.tuple [.unsupported .listComprehension])] ==
  some ⟨[], .unsupportedExpression .listComprehension⟩
#guard diagnose [.functionDef "f" [] [.return_ (some (.unsupported .bytesLiteral))]] ==
  some ⟨[0], .unsupportedExpression .bytesLiteral⟩

private def signatureScopes : List Stmt :=
  [.functionDef "outer" [] [
    .functionDef "f"
      [{ name := "args", kind := .varPositional, annotation := some (.name "TypeA") },
        { name := "k", kind := .keywordOnly, defaultValue := some (.name "defaultK") },
        { name := "options", kind := .varKeyword }]
      [.expression (.name "args"), .expression (.name "k"), .expression (.name "options")]
      [] (some (.name "TypeR")),
    .classDef "C" [] [.pass] []
      [(some "metaclass", .name "metatype"), (none, .name "classOptions")]]]

#guard inspect signatureScopes [0] "TypeA" == some .implicitGlobal
#guard inspect signatureScopes [0] "TypeR" == some .implicitGlobal
#guard inspect signatureScopes [0] "defaultK" == some .implicitGlobal
#guard inspect signatureScopes [0] "metaclass" == none
#guard inspect signatureScopes [0] "metatype" == some .implicitGlobal
#guard inspect signatureScopes [0] "classOptions" == some .implicitGlobal
#guard ["args", "k", "options"].all (fun name => inspect signatureScopes [0, 0] name == some .local)
#guard inspect signatureScopes [0, 0] "TypeA" == none
#guard ((analyze ⟨signatureScopes⟩ .deferred).toOption.bind (·.atPath [0])).map
  (fun scope => (scope.access "TypeA", scope.access "TypeR", scope.access "defaultK")) ==
  some (none, none, some .implicitGlobal)
#guard diagnose [.expression (.lambda [{ name := "x", annotation := some (.name "T") }] (.name "x"))] ==
  some ⟨[0], .lambdaParameterAnnotation "x"⟩

private def occurrenceFixture : List Stmt :=
  [.functionDef "f" [{ name := "x" }] [
    .globalDecl ["g"],
    .assign "x" (.binary .add (.name "x") (.name "x")),
    .delete "x",
    .return_ (some (.name "g"))]]

#guard ((analyze ⟨occurrenceFixture⟩).toOption.bind (·.atPath [0])).map (fun scope =>
  scope.occurrences.map (fun entry => (entry.occurrence, entry.access))) ==
  some [(⟨"x", .parameter⟩, .local), (⟨"g", .globalDeclaration⟩, .declaredGlobal),
    (⟨"x", .read⟩, .local), (⟨"x", .read⟩, .local), (⟨"x", .assign⟩, .local),
    (⟨"x", .delete⟩, .local), (⟨"g", .read⟩, .declaredGlobal)]
#guard ((analyze ⟨classScopes⟩).toOption.bind (·.atPath [0, 0, 0])).bind (fun scope =>
  scope.occurrences.getLast?.map (fun entry => (entry.occurrence, entry.access))) ==
  some (⟨"__class__", .implicitRead⟩, .free [0, 0])

#print axioms enclosingBinding_eq_some_iff
#print axioms enclosingBinding_stops
#print axioms enclosingBinding_skips_class
#print axioms enclosingBinding_classCell
#print axioms Scope.occurrence_access
