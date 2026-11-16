module

public import Silmaril.Project.Registry.Value.Defs
public import Silmaril.Project.Languages.Defs

/-!
# Silmaril projects: languages (layer 5)

The kinds that name **languages**, the domains they are over and the measures on them:

| kind | Lean checks | Lean fills |
|---|---|---|
| `language_domain N := T` | `T : Type` | `carrier`, `monoid` (a `Monoid T` instance exists), `letters` (`α` when `T` is `List α`) |
| `measure N := μ (domain := D)` | `μ : T → β` for `D`'s carrier `T` | `codomain` |
| `language_interpretation N := I (domain := D) (abi := A) (environment := E)` | `I : V → Set T`; `A` and `E`, when given, occur in `I`'s definition | `input` (`V`), `carrier` |
| `language N (domain := D) (op := …) …` | below; ill-typed combinations are rejected | `decl`, `term` (the definition as `ppOneLine` prints it, as instance arguments record it), `carrier`, `identity` (and `semantics` for `regex`) |

A **language** is a `Set T` over the carrier `T` of its domain (`Set (List UInt8)` for the
built-in `bytes` domain). Its `op` says how it is built; except for `decl`, Lean *generates* the
definition `N` (in the current namespace), so the language is its construction by definition:

| `op` | fields | definition |
|---|---|---|
| `decl` | `decl := L` | the existing `L : Set T` |
| `format` | `format := F` (domain `bytes`) | `Languages.formatLang F`: the byte strings the project format `F` parses |
| `artifact` | `value := X`, `interpretation := I` | `Languages.artifactLang X I`: the interpretation `I` of the value that the CID-pinned bytes of `X` parse to |
| `union`, `inter` | `args := [A, B, …]` | `A ∪ B ∪ …`, `A ∩ B ∩ …` (`Set.union`, `Set.inter`) |
| `diff` | `args := [A, B]` | `A \ B` (`Set.diff`) |
| `regex` | `decl := e`, `args := [L₀, …]` (the leaves) | `Regex.Expr.eval ![L₀, …] e` for a list domain `List α` (`e : Regex.Expr (Fin n) α`), else `MonoidRegex.Expr.eval ![L₀, …] e` for a domain with a `Monoid` (`e : MonoidRegex.Expr (Fin n) T`) |
| `within` | `args := [A]`, `measure := μ`, `bound := b` | `Languages.within A μ b`, for a measure into `ℕ` |

Every operand must be a language over the same domain (`union` of a byte language and a
language of numbers is an error), and an interpretation and a measure must be over the
language's domain.

**Identity.** `identity` describes the construction without any display name: the body of a
`decl` (fully qualified; the constant's name when its body is not visible), the format's definition, the CID and format of an artifact's bytes with
the interpretation's definition, ABI and environment, the operator with its operands'
identities, the regex expression's constant with its leaves' identities, and the domain's
carrier. Two languages with the same identity are the same construction; languages that are
*equal as sets* but built differently have different identities, and their equality is a
problem (`silmaril.shapes.language.eq_at`), not a tag. Identity is not the record name: renaming
a language, or giving it another title, does not change it.

The fields `title`, `doc` and `source` (a citation key of `references.bib`, or a section of a
standard) are kept as written.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command

/-- The record `(kind, name)`, which must be declared. -/
def needRecord (kind ofKind name : String) : CoreM Record := do
  let some r := findRecord? (← getEnv) ofKind name
    | throwError "silmaril {kind}: no `silmaril {ofKind} {name}` is declared or imported"
  return r

/-- The carrier of the domain `dom`. -/
def domainCarrier (kind dom : String) : CoreM Expr :=
  return mkConst (← recordDecl kind "language_domain" dom)

/-- `T` of a type `Set T`, if it is one (up to reducible unfolding). -/
def setArg? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR ty
  return if ty.isAppOfArity ``Set 1 then some (ty.getArg! 0) else none

/-- `Set T`. -/
def setOf (T : Expr) : Expr := mkApp (mkConst ``Set [Level.zero]) T

/-- `language_domain N := T`. -/
@[silmaril_kind language_domain] def languageDomainHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let name ← needName kind name?
    let d ← fs.const kind "decl"
    expectType kind m!"{d}" (← constType d) (.sort (Level.succ Level.zero))
    let T ← whnfR (mkConst d)
    let monoid ← try
        pure (← synthInstance? (mkApp (mkConst ``Monoid [Level.zero]) (mkConst d))).isSome
      catch _ => pure false
    let letters : Json ← if T.isAppOfArity ``List 1 then pure (.str (← ppOneLine (T.getArg! 0)))
      else pure .null
    let fs ← fs.push kind "carrier" (.str (← ppOneLine T))
    let fs ← fs.push kind "monoid" (.bool monoid)
    let fs ← fs.push kind "letters" letters
    return #[(name, fs)]

/-- `measure N := μ (domain := D)`, `μ : T → β`. -/
@[silmaril_kind measure] def measureHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let name ← needName kind name?
    let d ← fs.const kind "decl"
    let T ← domainCarrier kind (← fs.str kind "domain")
    let ty ← whnf (← constType d)
    let .forallE _ dom cod _ := ty
      | throwError "silmaril measure: {d} has type{indentExpr ty}\nbut a measure is a function on the domain's carrier"
    unless !cod.hasLooseBVars && (← isDefEq dom T) do
      throwError "silmaril measure: {d} has type{indentExpr ty}\nbut should be a function from{indentExpr T}"
    return #[(name, ← fs.push kind "codomain" (.str (← ppOneLine cod)))]

/-- The definition of `d`, which must be visible. -/
def visibleValue (kind : String) (d : Name) : CoreM Expr := do
  let some v := (← getConstInfo d).value?
    | throwError "silmaril {kind}: the definition of {d} is not visible; state it in an \
        `@[expose] public section`"
  return v

/-- `language_interpretation N := I (domain := D) (abi := A) (environment := E)`. -/
@[silmaril_kind language_interpretation] def languageInterpretationHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let name ← needName kind name?
    let d ← fs.const kind "decl"
    let T ← domainCarrier kind (← fs.str kind "domain")
    let ty ← whnf (← constType d)
    let .forallE _ V body _ := ty
      | throwError "silmaril {kind}: {d} has type{indentExpr ty}\nbut an interpretation is `V → Set T`"
    let ok ← if body.hasLooseBVars then pure false else isDefEq body (setOf T)
    unless ok do
      throwError "silmaril {kind}: {d} has type{indentExpr ty}\nbut should be `V → Set T` for the carrier{indentExpr T}"
    let used := (← visibleValue kind d).getUsedConstants
    for key in ["abi", "environment"] do
      if let some (_, c) := fs.consts.find? (·.1 == key) then
        unless used.contains c do
          throwError "silmaril {kind}: the {key} {c} does not occur in the definition of {d}; \
            the interpretation must be defined from it"
    let fs ← fs.push kind "input" (.str (← ppOneLine V))
    return #[(name, ← fs.push kind "carrier" (.str (← ppOneLine T)))]

/-- The operations of `language`. -/
def languageOps : List String := ["decl", "format", "artifact", "union", "inter", "diff", "regex",
  "within"]

/-- An operand: its definition and identity, checked to be over the domain `dom`. -/
def languageOperand (kind name dom : String) : CoreM (Name × Json) := do
  let r ← needRecord kind "language" name
  let some d := r.str? "decl" | throwError "silmaril {kind}: language {name.quote} has no `decl`"
  let some rdom := r.str? "domain" | throwError "silmaril {kind}: language {name.quote} has no domain"
  unless rdom == dom do
    throwError "silmaril {kind}: language {name.quote} is over the domain {rdom.quote}, not \
      {dom.quote}; the operands of a language must have its domain"
  return (d.toName, (r.get? "identity").getD .null)

/-- The `args` field: a list of names. -/
def nameList (fs : Fields) (kind key : String) : CoreM (Array String) := do
  match fs.get? key with
  | none => return #[]
  | some (.arr xs) => xs.mapM fun
      | .str s => pure s
      | _ => throwError "silmaril {kind}: `{key}` is a list of names"
  | some _ => throwError "silmaril {kind}: `{key}` is a list of names"

/-- `![x₀, …]` with elements of type `α`. -/
def vecOf (α : Expr) (xs : Array Expr) : MetaM Expr := do
  let mut v ← mkAppOptM ``Matrix.vecEmpty #[some α]
  for i in [0:xs.size] do
    let k := xs.size - 1 - i
    v ← mkAppOptM ``Matrix.vecCons #[some α, some (toExpr i), some xs[k]!, some v]
  return v

/-- Add the public, exposed definition `n : type := value`. -/
def addLanguageDef (n : Name) (type value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasFVar then
    throwError "silmaril language: the definition of {n} is not closed:{indentExpr value}"
  let vty ← inferType value
  unless ← isDefEq vty type do
    throwError "silmaril language: the construction has type{indentExpr vty}\nnot{indentExpr type}"
  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe n [] type value
    (.regular (getMaxHeight (← getEnv) value + 1)))) (forceExpose := true)
  addDeclarationRangesFromSyntax n (← getRef)

/-- The identity of an object: its fields, sorted by key. -/
def identityObj (kvs : List (String × Json)) : Json := Json.mkObj kvs

/-- `language N (domain := D) (op := …) …`. -/
@[silmaril_kind language] def languageHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let decl ← fullName name
    liftTermElabM do
    let dom ← fs.str kind "domain"
    let T ← domainCarrier kind dom
    let T' ← whnfR T
    let carrier ← ppOneLine T'
    let target := setOf T
    let op ← fs.str kind "op"
    unless languageOps.contains op do
      throwError "silmaril language: unknown op {op.quote}; expected one of {languageOps}"
    let args ← nameList fs kind "args"
    let mut fs := fs
    -- (value, identity fields); `none` for `decl`, which is not generated
    let (value?, ident) : Option Expr × List (String × Json) ← match op with
      | "decl" =>
        let d ← fs.const kind "decl"
        expectType kind m!"{d}" (← constType d) target
        unless args.isEmpty do throwError "silmaril language: op `decl` takes no `args`"
        -- a definition is identified by its (fully qualified) body, so two wrappers of one term
        -- (`JsonBytes.language .rfc8259`) are one construction; anything else by its name
        let term ← match (← getConstInfo d).value? with
          | some v => pure (some (← ppOneLine v))
          | none => pure none
        pure (none, match term with
          | some t => [("term", .str t)]
          | none => [("decl", .str d.toString)])
      | "format" =>
        unless ← isDefEq T (mkApp (mkConst ``List [Level.zero]) (mkConst ``UInt8)) do
          throwError "silmaril language: a format language is over bytes (`List UInt8`), not {carrier}"
        let fname ← fs.str kind "format"
        let F ← recordDecl kind "format" fname
        let (A, V) ← formatArgs kind F
        unless ← isDefEq A (mkConst ``Silmaril.Project.blob) do
          throwError "silmaril language: format {fname} reads{indentExpr A}\nnot blobs"
        pure (some (mkApp2 (mkConst ``Silmaril.Project.Languages.formatLang) V (mkConst F)),
          [("format", .str F.toString)])
      | "artifact" =>
        let xname ← fs.str kind "value"
        let xr ← needRecord kind "value" xname
        let some xd := xr.str? "decl" | throwError "silmaril language: value {xname} has no `decl`"
        let xty ← whnf (← constType xd.toName)
        unless xty.isAppOfArity ``Silmaril.Project.Value 1 do
          throwError "silmaril language: {xd} is not a `Value V`"
        let V := xty.getArg! 0
        let iname ← fs.str kind "interpretation"
        let ir ← needRecord kind "language_interpretation" iname
        unless ir.str? "domain" == some dom do
          throwError "silmaril language: interpretation {iname} is over the domain \
            {(ir.str? "domain").getD "?"}, not {dom}"
        let some id := ir.str? "decl" | throwError "silmaril language: interpretation {iname} has no `decl`"
        let I := mkConst id.toName
        let .forallE _ V' _ _ ← whnf (← inferType I) | throwError "silmaril language: bad interpretation"
        unless ← isDefEq V V' do
          throwError "silmaril language: value {xname} reads{indentExpr V}\nbut interpretation \
            {iname} interprets{indentExpr V'}"
        let src : Json := match xr.get? "sources" with
          | some (.arr ss) => match ss[0]? with
            | some s => Json.mkObj [("cid", (s.getObjValD "cid")), ("format", (s.getObjValD "format"))]
            | none => .null
          | _ => .null
        pure (some (mkAppN (mkConst ``Silmaril.Project.Languages.artifactLang [Level.zero])
            #[V, T, mkConst xd.toName, I]),
          [("bytes", src), ("interpretation", identityObj [("decl", .str id),
            ("abi", (ir.get? "abi").getD .null), ("environment", (ir.get? "environment").getD .null)])])
      | "union" | "inter" | "diff" =>
        if op == "diff" && args.size != 2 then
          throwError "silmaril language: op `diff` takes exactly two `args`"
        if args.size < 2 then throwError "silmaril language: op `{op}` takes at least two `args`"
        let ops ← args.mapM (languageOperand kind · dom)
        let f := match op with
          | "union" => ``Set.union | "inter" => ``Set.inter | _ => ``Set.diff
        let mut v := mkConst ops[0]!.1
        for (d, _) in ops[1:] do v ← mkAppM f #[v, mkConst d]
        pure (some v, [("args", .arr (ops.map (·.2)))])
      | "regex" =>
        let e ← fs.const kind "decl"
        let ops ← args.mapM (languageOperand kind · dom)
        let n := ops.size
        let fin := mkApp (mkConst ``Fin) (toExpr n)
        let (sem, v) ← if T'.isAppOfArity ``List 1 then do
            let α := T'.getArg! 0
            expectType kind m!"the regular expression {e}" (← constType e)
              (← mkAppM ``Silmaril.Accept.Regex.Expr #[fin, α])
            let ρ ← vecOf (mkApp (mkConst ``Language [Level.zero]) α) (ops.map (mkConst ·.1))
            pure ("list", ← mkAppM ``Silmaril.Accept.Regex.Expr.eval #[ρ, mkConst e])
          else do
            let some _ ← (try synthInstance? (mkApp (mkConst ``Monoid [Level.zero]) T) catch _ => pure none)
              | throwError "silmaril language: the domain {dom} ({carrier}) is neither a list type \
                  nor a monoid, so a regular expression has no meaning over it"
            expectType kind m!"the regular expression {e}" (← constType e)
              (← mkAppM ``Silmaril.Accept.MonoidRegex.Expr #[fin, T])
            let ρ ← vecOf target (ops.map (mkConst ·.1))
            pure ("monoid", ← mkAppM ``Silmaril.Accept.MonoidRegex.Expr.eval #[ρ, mkConst e])
        fs := (fs.erase "decl")
        fs ← fs.push kind "regex" (.str e.toString)
        fs ← fs.push kind "semantics" (.str sem)
        pure (some v, [("expr", .str e.toString), ("semantics", .str sem),
          ("leaves", .arr (ops.map (·.2)))])
      | _ => -- within
        unless args.size == 1 do throwError "silmaril language: op `within` takes one language in `args`"
        let (L, lid) ← languageOperand kind args[0]! dom
        let mname ← fs.str kind "measure"
        let mr ← needRecord kind "measure" mname
        unless mr.str? "domain" == some dom do
          throwError "silmaril language: measure {mname} is not over the domain {dom}"
        let some md := mr.str? "decl" | throwError "silmaril language: measure {mname} has no `decl`"
        let some (.num ⟨b, 0⟩) := fs.get? "bound"
          | throwError "silmaril language: op `within` needs `(bound := <natural number>)`"
        unless b ≥ 0 do throwError "silmaril language: the bound is a natural number"
        let μ := mkConst md.toName
        let .forallE _ _ cod _ ← whnf (← inferType μ) | throwError "silmaril language: bad measure"
        unless ← isDefEq cod (mkConst ``Nat) do
          throwError "silmaril language: op `within` needs a measure into ℕ; {mname} is into{indentExpr cod}"
        pure (some (mkAppN (mkConst ``Silmaril.Project.Languages.within [Level.zero])
            #[T, mkConst L, μ, toExpr b.toNat]),
          [("of", lid), ("measure", .str md), ("bound", toJson b.toNat)])
    let declName ← match value? with
      | none => fs.const kind "decl"
      | some v => do
        if (← getEnv).contains decl then
          throwError "silmaril language: {decl} is already declared"
        addLanguageDef decl target v
        fs ← fs.push kind "decl" (.str decl.toString)
        pure decl
    -- the definition as instance arguments record it (`ppOneLine`, so with the same escapes:
    -- `«silmaril».…`), which is how the database relates problems to languages
    fs ← fs.push kind "term" (.str (← ppOneLine (mkConst declName)))
    fs ← fs.push kind "carrier" (.str carrier)
    fs ← fs.push kind "identity"
      (identityObj ([("op", .str op), ("carrier", .str carrier)] ++ ident))
    return #[(name, fs)]

end Silmaril.Project
