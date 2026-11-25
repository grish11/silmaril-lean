# TLA+ Surface S-expression schema v1

The wire format represents the named [TLA+ Surface AST](tla.md#tla-surface-syntax).
Import [Defs](../../Silmaril/ProofFormats/TLA/SurfaceSExp/Defs.lean) for the
codec or [Thms](../../Silmaril/ProofFormats/TLA/SurfaceSExp/Thms.lean) for
its laws. Both modules use the namespace `Silmaril.ProofFormats.TLA.SurfaceSExp`.

## Envelope and field types

```text
(tla-surface 1 PAYLOAD)
```

`PAYLOAD` is a `Module` or `Expr` as selected by the entry point. All tags are
case-sensitive symbols. Every constructor is a proper list of its tag and
exactly the fields in the table, in the order shown. A nullary constructor
is a one-element list. Schema v1 fixes these tags, field counts, types and
positions. Changing them requires a new version.

| Field type | Version 1 representation |
| --- | --- |
| `Name` (`Surface.Ident`) | `(name "text")`, where the field is a string atom. |
| `Text` (`String`) | One double-quoted string atom. This preserves decoded literal content, fractional text and operator spelling exactly. |
| `Nat` | A symbol matching `0` or `[1-9][0-9]*` in ASCII. It has arbitrary precision. |
| `Bool` | The symbol `false` or `true`. |
| `List<T>` | `(list T ...)`, in order. The empty list field is `(list)`. |
| `Option<T>` | `(none)` or `(some T)`. |

Version 1 uses the verified [DottedSExp syntax](../../Silmaril/Formats/SExp/Dotted/Defs.lean).
Use UTF-8 for bytes. To emit canonical text, use bare symbols for the tags,
version, Booleans and numbers. Write strings in double quotes, escaping
backslash as `\\`, quote as `\"`, newline as `\n`, carriage return as `\r`,
and tab as `\t`. Emit other Unicode scalar values verbatim. Write each
proper list with parentheses and a single ASCII space between items.
The writer emits one datum with no leading or trailing whitespace.
An infix tree with operator spelling `:=` can be represented by this datum
with whitespace added for readability.

```lisp
(tla-surface 1
  (expr-infix (infix-op-symbol ":=")
    (expr-ref (ref-head-operator (operator-name-ident (name "x"))) (list) (list))
    (expr-literal (literal-natural 7))))
```

The decoder checks the envelope, tag, arity, field shapes, child sorts and
natural number spellings. Any improper list in a schema position fails.
Text and byte decoding consume exactly one datum and allow the underlying
reader's whitespace, semicolon comments, quoting and escapes. Dotted text
whose cdr is itself a proper list can denote the same proper tree.
An additional top-level datum, trailing invalid syntax or invalid UTF-8
fails. The text writer chooses a single spelling for each tree.

The codec preserves every value of the Surface types. In particular
`Literal.decimal` stores its whole part as a canonical `Nat` and its
fractional part as exact `Text`, including leading or trailing zeroes.
Identifier syntax, fractional digit validity, reserved operators, list
nonemptiness, binding and other TLA+ checks belong to later passes.

## Constructor table

Types in the table refer to Surface sorts or the field types above. Field
names describe the positions and are omitted on the wire.

| Surface sort | Tag | Positional fields |
| --- | --- | --- |
| `Literal` | `literal-natural` | `value : Nat` |
| `Literal` | `literal-decimal` | `whole : Nat`, `fractionalDigits : Text` |
| `Literal` | `literal-string` | `value : Text` |
| `PrefixOp` | `prefix-op-negation` | — |
| `PrefixOp` | `prefix-op-minus` | — |
| `PrefixOp` | `prefix-op-enabled` | — |
| `PrefixOp` | `prefix-op-unchanged` | — |
| `PrefixOp` | `prefix-op-always` | — |
| `PrefixOp` | `prefix-op-eventually` | — |
| `PrefixOp` | `prefix-op-subset` | — |
| `PrefixOp` | `prefix-op-union` | — |
| `PrefixOp` | `prefix-op-domain` | — |
| `PrefixOp` | `prefix-op-symbol` | `spelling : Text` |
| `InfixOp` | `infix-op-compose` | — |
| `InfixOp` | `infix-op-leads-to` | — |
| `InfixOp` | `infix-op-guarantees` | — |
| `InfixOp` | `infix-op-symbol` | `spelling : Text` |
| `PostfixOp` | `postfix-op-prime` | — |
| `PostfixOp` | `postfix-op-symbol` | `spelling : Text` |
| `Symbol` | `symbol-prefix` | `op : PrefixOp` |
| `Symbol` | `symbol-infix` | `op : InfixOp` |
| `Symbol` | `symbol-postfix` | `op : PostfixOp` |
| `OperatorName` | `operator-name-ident` | `name : Name` |
| `OperatorName` | `operator-name-symbolic` | `op : Symbol` |
| `OperatorDecl` | `operator-decl-ident` | `name : Name`, `arity : Nat` |
| `OperatorDecl` | `operator-decl-symbolic` | `op : Symbol` |
| `OperatorHead` | `operator-head-ident` | `name : Name`, `parameters : List<OperatorDecl>` |
| `OperatorHead` | `operator-head-prefix` | `op : PrefixOp`, `arg : Name` |
| `OperatorHead` | `operator-head-infix` | `left : Name`, `op : InfixOp`, `right : Name` |
| `OperatorHead` | `operator-head-postfix` | `arg : Name`, `op : PostfixOp` |
| `BoundPattern` | `bound-pattern-ident` | `name : Name` |
| `BoundPattern` | `bound-pattern-tuple` | `names : List<Name>` |
| `BoundNames` | `bound-names-names` | `names : List<Name>` |
| `BoundNames` | `bound-names-tuple` | `names : List<Name>` |
| `Quantifier` | `quantifier-exists` | — |
| `Quantifier` | `quantifier-forall` | — |
| `Junction` | `junction-conjunction` | — |
| `Junction` | `junction-disjunction` | — |
| `ActionBracket` | `action-bracket-square` | — |
| `ActionBracket` | `action-bracket-angle` | — |
| `Fairness` | `fairness-weak` | — |
| `Fairness` | `fairness-strong` | — |
| `StructuralSelector` | `structural-selector-operand` | `index : Nat` |
| `StructuralSelector` | `structural-selector-left` | — |
| `StructuralSelector` | `structural-selector-right` | — |
| `StructuralSelector` | `structural-selector-body` | — |
| `StructuralSelector` | `structural-selector-all-bindings` | — |
| `StepRefLevel` | `step-ref-level-explicit` | `level : Nat` |
| `StepRefLevel` | `step-ref-level-current` | — |
| `StepRef` | `step-ref` | `level : StepRefLevel`, `name : Name` |
| `RefHead` | `ref-head-operator` | `name : OperatorName` |
| `RefHead` | `ref-head-step` | `reference : StepRef` |
| `Label` | `label` | `name : Name`, `parameters : List<Name>` |
| `Visibility` | `visibility-ordinary` | — |
| `Visibility` | `visibility-local` | — |
| `Expr` | `expr-ref` | `head : RefHead`, `args : List<OpArg>`, `selectors : List<Selector>` |
| `Expr` | `expr-literal` | `value : Literal` |
| `Expr` | `expr-prefix` | `op : PrefixOp`, `arg : Expr` |
| `Expr` | `expr-infix` | `op : InfixOp`, `left : Expr`, `right : Expr` |
| `Expr` | `expr-postfix` | `op : PostfixOp`, `arg : Expr` |
| `Expr` | `expr-cartesian` | `factors : List<Expr>` |
| `Expr` | `expr-junction` | `kind : Junction`, `items : List<Expr>` |
| `Expr` | `expr-if-then-else` | `condition : Expr`, `consequent : Expr`, `alternative : Expr` |
| `Expr` | `expr-cases` | `arms : List<CaseArm>`, `other : Option<Expr>` |
| `Expr` | `expr-let-in` | `declarations : List<LetDecl>`, `body : Expr` |
| `Expr` | `expr-rigid-quant` | `quantifier : Quantifier`, `binders : RigidBinders`, `body : Expr` |
| `Expr` | `expr-temporal-quant` | `quantifier : Quantifier`, `names : List<Name>`, `body : Expr` |
| `Expr` | `expr-choose` | `pattern : BoundPattern`, `domain : Option<Expr>`, `predicate : Expr` |
| `Expr` | `expr-set-enum` | `elements : List<Expr>` |
| `Expr` | `expr-set-filter` | `pattern : BoundPattern`, `domain : Expr`, `predicate : Expr` |
| `Expr` | `expr-set-map` | `body : Expr`, `bounds : List<Bound>` |
| `Expr` | `expr-function` | `bounds : List<Bound>`, `body : Expr` |
| `Expr` | `expr-function-set` | `domain : Expr`, `range : Expr` |
| `Expr` | `expr-index` | `fn : Expr`, `args : List<Expr>` |
| `Expr` | `expr-tuple` | `elements : List<Expr>` |
| `Expr` | `expr-record` | `fields : List<Field>` |
| `Expr` | `expr-record-set` | `fields : List<Field>` |
| `Expr` | `expr-field` | `record : Expr`, `name : Name` |
| `Expr` | `expr-except` | `base : Expr`, `updates : List<Update>` |
| `Expr` | `expr-old-value` | — |
| `Expr` | `expr-action` | `kind : ActionBracket`, `body : Expr`, `subscript : Expr` |
| `Expr` | `expr-fairness` | `kind : Fairness`, `subscript : Expr`, `action : Expr` |
| `Expr` | `expr-labeled` | `label : Label`, `body : Expr` |
| `OpArg` | `op-arg-expr` | `value : Expr` |
| `OpArg` | `op-arg-symbolic` | `op : Symbol` |
| `OpArg` | `op-arg-lambda` | `parameters : List<Name>`, `body : Expr` |
| `Selector` | `selector-named` | `name : OperatorName`, `args : List<OpArg>` |
| `Selector` | `selector-arguments` | `args : List<OpArg>` |
| `Selector` | `selector-structural` | `selector : StructuralSelector` |
| `Bound` | `bound` | `names : BoundNames`, `domain : Expr` |
| `RigidBinders` | `rigid-binders-unbounded` | `names : List<Name>` |
| `RigidBinders` | `rigid-binders-bounded` | `groups : List<Bound>` |
| `CaseArm` | `case-arm` | `condition : Expr`, `result : Expr` |
| `Field` | `field` | `name : Name`, `value : Expr` |
| `UpdateComponent` | `update-component-field` | `name : Name` |
| `UpdateComponent` | `update-component-index` | `args : List<Expr>` |
| `Update` | `update` | `path : List<UpdateComponent>`, `value : Expr` |
| `Substitution` | `substitution` | `target : OperatorName`, `replacement : OpArg` |
| `Instantiation` | `instantiation` | `moduleName : Name`, `substitutions : List<Substitution>` |
| `Definition` | `definition-operator` | `visibility : Visibility`, `head : OperatorHead`, `body : Expr` |
| `Definition` | `definition-function` | `visibility : Visibility`, `name : Name`, `bounds : List<Bound>`, `body : Expr` |
| `Definition` | `definition-named-instance` | `visibility : Visibility`, `name : Name`, `parameters : List<OperatorDecl>`, `instanceBody : Instantiation` |
| `LetDecl` | `let-decl-definition` | `value : Definition` |
| `LetDecl` | `let-decl-recursive` | `operators : List<OperatorDecl>` |
| `SymbolLevel` | `symbol-level-constant` | — |
| `SymbolLevel` | `symbol-level-state` | — |
| `SymbolLevel` | `symbol-level-action` | — |
| `SymbolLevel` | `symbol-level-temporal` | — |
| `AssumeProveMode` | `assume-prove-mode-plain` | — |
| `AssumeProveMode` | `assume-prove-mode-boxed` | — |
| `Statement` | `statement-expr` | `value : Expr` |
| `Statement` | `statement-assume-prove` | `assumeMode : AssumeProveMode`, `hypotheses : List<Hypothesis>`, `proveMode : AssumeProveMode`, `goal : Expr` |
| `Statement` | `statement-labeled` | `name : Name`, `statement : Statement` |
| `Hypothesis` | `hypothesis-statement` | `value : Statement` |
| `Hypothesis` | `hypothesis-new-symbol` | `level : SymbolLevel`, `declaration : OperatorDecl` |
| `Hypothesis` | `hypothesis-new-variable` | `name : Name` |
| `Hypothesis` | `hypothesis-new-bound-constant` | `name : Name`, `domain : Expr` |
| `Citation` | `citation-expr` | `value : Expr` |
| `Citation` | `citation-module-name` | `name : Name` |
| `Citations` | `citations` | `facts : List<Citation>`, `defs : List<Citation>` |
| `Directive` | `directive-use` | `only : Bool`, `citations : Citations` |
| `Directive` | `directive-hide` | `citations : Citations` |
| `StepLevel` | `step-level-explicit` | `level : Nat` |
| `StepLevel` | `step-level-current` | — |
| `StepLevel` | `step-level-next` | — |
| `StepLabel` | `step-label` | `level : StepLevel`, `name : Option<Name>` |
| `Proof` | `proof-obvious` | — |
| `Proof` | `proof-omitted` | — |
| `Proof` | `proof-by-facts` | `only : Bool`, `citations : Citations` |
| `Proof` | `proof-steps` | `steps : List<ProofStep>`, `qedLabel : StepLabel`, `qedProof : Option<Proof>` |
| `ProofStep` | `proof-step` | `label : StepLabel`, `body : StepBody` |
| `StepBody` | `step-body-directive` | `value : Directive` |
| `StepBody` | `step-body-instantiation` | `value : Instantiation` |
| `StepBody` | `step-body-define` | `definitions : List<Definition>` |
| `StepBody` | `step-body-have` | `value : Expr` |
| `StepBody` | `step-body-take` | `binders : RigidBinders` |
| `StepBody` | `step-body-witness` | `values : List<Expr>` |
| `StepBody` | `step-body-pick` | `binders : RigidBinders`, `predicate : Expr`, `proof : Option<Proof>` |
| `StepBody` | `step-body-case-of` | `condition : Expr`, `proof : Option<Proof>` |
| `StepBody` | `step-body-assert` | `statement : Statement`, `proof : Option<Proof>` |
| `StepBody` | `step-body-suffices` | `statement : Statement`, `proof : Option<Proof>` |
| `Theorem` | `theorem` | `name : Option<Name>`, `statement : Statement`, `proof : Option<Proof>` |
| `Module` | `module` | `name : Name`, `extendsModules : List<Name>`, `units : List<ModuleUnit>` |
| `ModuleUnit` | `module-unit-variables` | `names : List<Name>` |
| `ModuleUnit` | `module-unit-constants` | `operators : List<OperatorDecl>` |
| `ModuleUnit` | `module-unit-recursive` | `operators : List<OperatorDecl>` |
| `ModuleUnit` | `module-unit-definition` | `value : Definition` |
| `ModuleUnit` | `module-unit-instantiation` | `visibility : Visibility`, `value : Instantiation` |
| `ModuleUnit` | `module-unit-assumption` | `name : Option<Name>`, `body : Expr` |
| `ModuleUnit` | `module-unit-theorem-decl` | `value : Theorem` |
| `ModuleUnit` | `module-unit-submodule` | `value : Module` |
| `ModuleUnit` | `module-unit-directive` | `value : Directive` |

## Lean contract

The `encodeModule` and `encodeExpr` functions produce `Tree`, an alias for
`DottedSExp.Datum`. Corresponding `decode` functions return `Except DecodeError`.
The `Text` entry points use `String` and the `Bytes` entry points use
`Silmaril.Formats.Bytes`. In either case the transport decoder passes the parsed tree
to the AST decoder.

- `decodeModule_encodeModule` and `decodeExpr_encodeExpr` prove recovery for
  every value. The decoder folds the input cons tree structurally to
  obtain each node's proper-list view and typed child readers.
- `encodeModule_of_decodeModule` and `encodeExpr_of_decodeExpr` prove that
  a successful decode re-encodes to the exact input tree. The decoder
  performs this equality check using the decidable equality of `SExp2`.
- The `Text` round trips compose tree recovery with
  `DottedSExp.parse?_print`. The `Bytes` round trips compose it with
  `DottedSExp.decode_encode`, which also checks that UTF-8 decoding inverts
  the library's encoding. These laws concern the writer's output and the
  exact parsed tree. Accepted whitespace or escape spellings need not
  survive printing.
