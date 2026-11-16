module

public import Silmaril.Project.Registry.Defs
public import Silmaril.Project.Registry.Language.Defs
public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Project.ConsequenceSystems.Defs

/-!
# Silmaril projects: consequence systems (layer 5)

The kind that names **consequence systems** (`docs/projects/consequence-systems.md`): a
`Silmaril.Consequence.System Ax C`, that is a relation `S : Ax → C → Prop` between contexts and
conclusions, `S Γ φ` read "`Γ ⊢ φ`" (`Silmaril.Logic.Consequence.Defs`). Nothing about `Ax` is assumed: a context may be a list (a finite
sequence `C₁, …, Cₙ`), a finite set, a multiset or a single formula, and **no structural rule
is implicit** — a system is reflexive, monotone or closed under cut only if a proof says so.

| kind | Lean checks | Lean fills |
|---|---|---|
| `consequence_system N := S` | `S : Ax → C → Prop` (universe-monomorphic) | `contexts` (`Ax`), `conclusions` (`C`), `term`, the typed shape (below) |
| `consequence_system N (op := union) (args := [A, B, …])` | two or more operands, over the same `Ax` and `C` (definitionally) | `decl := A ⊔ B ⊔ …` |
| `consequence_system N (op := inter) (args := [A, B, …])` | as for `union` | `decl := A ⊓ B ⊓ …` |
| `consequence_system N (op := diff) (args := [A, B])` | exactly two operands | `decl := A \ B` |
| `consequence_interpretation N := I (abi := A) (environment := E)` | `I : V → System Ax C`; `A` and `E`, when given, occur in `I`'s definition | `input` (`V`), `contexts`, `conclusions` |
| `consequence_system N (op := artifact) (value := X) (interpretation := I)` | `X` a registered `Value V`, `I` a registered `consequence_interpretation` reading `V` | `decl := ConsequenceSystems.artifactSystem X I` |
| `consequence_system N := W (op := erase)` | `W : Ax → C → Type` (a `WSystem`: a type of derivations of each `Γ ⊢ φ`) | `witness := W`, `decl := WSystem.erase W` (`Nonempty (W Γ φ)`) |

**Typed shape.** Lean classifies each side from its type (the `Expr`, up to reducible
unfolding): `ctx_kind`/`concl_kind` is `unit`, `list`, `finset`, `set` or `other` (a scalar
carrier), with the element type (`ctx_elem`/`concl_elem`) and whether that element type is
`Signed A` (`ctx_signed`/`concl_signed`, separately: mixed polarity is visible as such).
`raw_sequent` says both sides are lists of definitionally equal element types — a raw sequent
relation; that it is closed under any Gentzen rules is a separate problem
(`silmaril.shapes.consequence.gentzen_closed`).

`term` is the defining constant as the arguments of an instance print it, so that the database
can relate a problem to the system it names. Except for `op := decl` (the default), Lean *generates* the definition `N` in the current
namespace, so the system is its construction by definition. `⊔`, `⊓` and `\` are Mathlib's
pointwise lattice operations on `Ax → C → Prop` (`(A ⊔ B) Γ φ ↔ A Γ φ ∨ B Γ φ`, by `Iff.rfl`).
The operands of `union` and `inter` must be at least two, so that no empty union (the empty
system) or empty intersection (the universal system) is formed implicitly; register those
with `op := decl`. `diff` is binary, never an n-ary fold.

Operands are compatible when their context types and their conclusion types are
*definitionally equal* in Lean (checked with `isDefEq`, not by comparing printed names).

**Artifacts.** `op := artifact` mirrors `language … (op := artifact)`: the system is
`artifactSystem X I`, `Γ ⊢ φ` iff the CID-pinned bytes of `X` decode to some `v` with
`I v Γ φ`. A decode failure gives `⊥`, which is not a verified empty checker; the value's `.is`
certificate is what ties the system to a Lean module (`artifactSystem_of_is`). That the ABI and
environment occur in `I`'s definition is a sanity check of the metadata, not a proof that the
definition models execution.

The fields `title`, `doc` and `source` (a citation key of `references.bib`, or a section of a
standard) are kept as written.

What is *true* of a system — that it derives something, that a context derives everything,
that it derives a chosen `ff`, that it is sound or complete for another system, that a
translation preserves it — is a problem, stated with the standard shapes
`silmaril.shapes.consequence.*` (`Silmaril.Project.Shapes.Consequence.Defs`) and answered by
Lean proofs (`@[answers]`). The registry records no such property as a tag.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command

/-- The operations of `consequence_system`. -/
def consequenceOps : List String := ["decl", "union", "inter", "diff", "erase", "artifact"]

/-- `(Ax, C)` if `ty` is `Ax → C → s` (up to unfolding) with `s` the sort `Prop`
(`wantType := false`) or `Type` (`wantType := true`), and `C`, `s` not depending on the
bound variables. -/
def consequenceTypes? (ty : Expr) (wantType : Bool) : MetaM (Option (Expr × Expr)) := do
  let .forallE _ Ax b _ ← whnf ty | return none
  -- a dependent family `∀ Γ, C Γ → …` is not a consequence system
  if b.hasLooseBVars then return none
  let .forallE _ C body _ ← whnf b | return none
  if C.hasLooseBVars || body.hasLooseBVars then return none
  let s := if wantType then Expr.sort (Level.succ Level.zero) else Expr.sort Level.zero
  return if ← isDefEq (← whnf body) s then some (Ax, C) else none

/-- The context and conclusion types of the constant `d`, a system `Ax → C → Prop`. -/
def systemTypes (kind : String) (d : Name) : MetaM (Expr × Expr) := do
  unless (← getConstInfo d).levelParams.isEmpty do
    throwError "silmaril {kind}: {d} has universe parameters; register a universe-monomorphic system"
  let ty ← constType d
  let some r ← consequenceTypes? ty false
    | throwError "silmaril {kind}: {d} has type{indentExpr ty}\nbut a consequence system is \
        `Ax → C → Prop` (contexts to conclusions)"
  return r

/-- An operand: a registered system's definition, checked to be over `Ax` and `C`. -/
def consequenceOperand (kind name : String) (expected : Option (Expr × Expr)) :
    MetaM (Name × Expr × Expr) := do
  let some r := findRecord? (← getEnv) "consequence_system" name
    | throwError "silmaril {kind}: no `silmaril consequence_system {name}` is declared or imported"
  let some d := r.str? "decl" | throwError "silmaril {kind}: system {name} has no `decl`"
  let d := d.toName
  let (ax, c) ← systemTypes kind d
  if let some (Ax, C) := expected then
    unless ← isDefEq ax Ax do
      throwError "silmaril {kind}: system {name} has contexts{indentExpr ax}\nnot{indentExpr Ax}\n\
        the operands of a construction must have the same context type"
    unless ← isDefEq c C do
      throwError "silmaril {kind}: system {name} has conclusions{indentExpr c}\nnot{indentExpr C}\n\
        the operands of a construction must have the same conclusion type"
  return (d, ax, c)

/-- The carrier kind of one side of a system, read from its type `T` (up to reducible
unfolding, from the `Expr`, never from printed text): `unit` (`Unit` or `PUnit`), `list`, `finset`
or `set` with their element type, else `other` (a scalar carrier, the type itself as element).
Also whether the element type is `Silmaril.Consequence.Signed A`. -/
def carrierKind (T : Expr) : MetaM (String × Expr × Bool) := do
  let T ← whnfR T
  let (k, e) :=
    if T.isConstOf ``Unit || T.isAppOfArity ``PUnit 0 || T.isConstOf ``PUnit then ("unit", T)
    else if T.isAppOfArity ``List 1 then ("list", T.getArg! 0)
    else if T.isAppOfArity `Finset 1 then ("finset", T.getArg! 0)
    else if T.isAppOfArity ``Set 1 then ("set", T.getArg! 0)
    else ("other", T)
  let e ← whnfR e
  return (k, e, e.isAppOfArity `Silmaril.Consequence.Signed 1)

/-- The typed shape of a system `Ax → C → Prop`, as fields: each side's kind, element type and
polarity (`ctx_signed`, `concl_signed`, separately), and `raw_sequent` (both sides lists of
definitionally equal element types: a raw sequent relation, not a claim that any rule is
closed). -/
def systemShapeFields (kind : String) (fs : Fields) (Ax C : Expr) : TermElabM Fields := do
  let (ck, ce, cs) ← carrierKind Ax
  let (dk, de, ds) ← carrierKind C
  let seq ← if ck == "list" && dk == "list" then isDefEq ce de else pure false
  let mut fs := fs
  fs ← fs.push kind "ctx_kind" (.str ck)
  fs ← fs.push kind "ctx_elem" (.str (← ppOneLine ce))
  fs ← fs.push kind "ctx_signed" (.bool cs)
  fs ← fs.push kind "concl_kind" (.str dk)
  fs ← fs.push kind "concl_elem" (.str (← ppOneLine de))
  fs ← fs.push kind "concl_signed" (.bool ds)
  fs.push kind "raw_sequent" (.bool seq)

/-- Add the public, exposed definition `n : type := value`. -/
def addConsequenceDef (n : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasFVar then
    throwError "silmaril consequence_system: the definition of {n} is not closed:{indentExpr value}"
  let type ← instantiateMVars (← inferType value)
  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe n [] type value
    (.regular (getMaxHeight (← getEnv) value + 1)))) (forceExpose := true)
  addDeclarationRangesFromSyntax n (← getRef)

/-- `consequence_interpretation N := I (abi := A) (environment := E)`, `I : V → System Ax C`. -/
@[silmaril_kind consequence_interpretation] def consequenceInterpretationHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let name ← needName kind name?
    let d ← fs.const kind "decl"
    unless (← getConstInfo d).levelParams.isEmpty do
      throwError "silmaril {kind}: {d} has universe parameters; register a universe-monomorphic interpretation"
    let ty ← whnf (← constType d)
    let .forallE _ V body _ := ty
      | throwError "silmaril {kind}: {d} has type{indentExpr ty}\nbut an interpretation is `V → System Ax C`"
    let some (Ax, C) ← (if body.hasLooseBVars then pure none else consequenceTypes? body false)
      | throwError "silmaril {kind}: {d} has type{indentExpr ty}\nbut an interpretation is `V → System Ax C`"
    let used := (← visibleValue kind d).getUsedConstants
    for key in ["abi", "environment"] do
      if let some (_, c) := fs.consts.find? (·.1 == key) then
        unless used.contains c do
          throwError "silmaril {kind}: the {key} {c} does not occur in the definition of {d}; \
            the interpretation must be defined from it"
    let fs ← fs.push kind "input" (.str (← ppOneLine V))
    let fs ← fs.push kind "contexts" (.str (← ppOneLine Ax))
    return #[(name, ← fs.push kind "conclusions" (.str (← ppOneLine C)))]

/-- `consequence_system N := S`, or a construction (`op := union | inter | diff | erase`). -/
@[silmaril_kind consequence_system] def consequenceSystemHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let decl ← fullName name
    liftTermElabM do
    let op := match fs.get? "op" with | some (.str s) => s | _ => "decl"
    unless consequenceOps.contains op do
      throwError "silmaril {kind}: unknown op {op.quote}; expected one of {consequenceOps}"
    let args ← match fs.get? "args" with
      | none => pure #[]
      | some (.arr xs) => xs.mapM fun
          | .str s => pure s
          | _ => throwError "silmaril {kind}: `args` is a list of system names"
      | some _ => throwError "silmaril {kind}: `args` is a list of system names"
    let mut fs := fs
    if (fs.get? "op").isNone then fs ← fs.push kind "op" (.str "decl")
    let (d, Ax, C) ← match op with
      | "decl" =>
        unless args.isEmpty do throwError "silmaril {kind}: op `decl` takes no `args`"
        let d ← fs.const kind "decl"
        let (Ax, C) ← systemTypes kind d
        pure (d, Ax, C)
      | "erase" =>
        unless args.isEmpty do throwError "silmaril {kind}: op `erase` takes no `args`"
        let W ← fs.const kind "decl"
        unless (← getConstInfo W).levelParams.isEmpty do
          throwError "silmaril {kind}: {W} has universe parameters; register a universe-monomorphic witness system"
        let wty ← constType W
        let some (Ax, C) ← consequenceTypes? wty true
          | throwError "silmaril {kind}: {W} has type{indentExpr wty}\nbut a witness system is \
              `Ax → C → Type` (a type of derivations of each `Γ ⊢ φ`)"
        if (← getEnv).contains decl then throwError "silmaril {kind}: {decl} is already declared"
        -- `Silmaril.Consequence.WSystem.erase.{0,0,0} Ax C W`
        addConsequenceDef decl (mkApp3 (mkConst ``Silmaril.Consequence.WSystem.erase
          [Level.zero, Level.zero, Level.zero]) Ax C (mkConst W))
        fs := fs.erase "decl"
        fs ← fs.push kind "witness" (.str W.toString)
        fs ← fs.push kind "decl" (.str decl.toString)
        pure (decl, Ax, C)
      | "artifact" =>
        unless args.isEmpty do throwError "silmaril {kind}: op `artifact` takes no `args`"
        if (fs.get? "decl").isSome then throwError "silmaril {kind}: op `artifact` generates `decl`; do not give it"
        let xname ← fs.str kind "value"
        let xr ← needRecord kind "value" xname
        let some xd := xr.str? "decl" | throwError "silmaril {kind}: value {xname} has no `decl`"
        let xty ← whnf (← constType xd.toName)
        unless xty.isAppOfArity ``Silmaril.Project.Value 1 do
          throwError "silmaril {kind}: {xd} is not a `Value V`"
        let V := xty.getArg! 0
        let iname ← fs.str kind "interpretation"
        let ir ← needRecord kind "consequence_interpretation" iname
        let some id := ir.str? "decl"
          | throwError "silmaril {kind}: interpretation {iname} has no `decl`"
        let I := mkConst id.toName
        let .forallE _ V' body _ ← whnf (← inferType I)
          | throwError "silmaril {kind}: bad interpretation {iname}"
        unless ← isDefEq V V' do
          throwError "silmaril {kind}: value {xname} reads{indentExpr V}\nbut interpretation \
            {iname} interprets{indentExpr V'}"
        let some (Ax, C) ← consequenceTypes? body false
          | throwError "silmaril {kind}: bad interpretation {iname}"
        if (← getEnv).contains decl then throwError "silmaril {kind}: {decl} is already declared"
        addConsequenceDef decl (mkAppN (mkConst ``Silmaril.Project.ConsequenceSystems.artifactSystem)
          #[V, Ax, C, mkConst xd.toName, I])
        fs ← fs.push kind "decl" (.str decl.toString)
        pure (decl, Ax, C)
      | _ => -- union, inter, diff
        if op == "diff" && args.size != 2 then
          throwError "silmaril {kind}: op `diff` takes exactly two `args` (A \\ B)"
        if args.size < 2 then
          throwError "silmaril {kind}: op `{op}` takes at least two `args`; register the empty or \
            universal system with `op := decl`"
        if (fs.get? "decl").isSome then throwError "silmaril {kind}: op `{op}` generates `decl`; do not give it"
        let (d₀, Ax, C) ← consequenceOperand kind args[0]! none
        let mut v := mkConst d₀
        for a in args[1:] do
          let (d, _, _) ← consequenceOperand kind a (some (Ax, C))
          let f := match op with | "union" => ``Max.max | "inter" => ``Min.min | _ => ``SDiff.sdiff
          v ← mkAppM f #[v, mkConst d]
        if (← getEnv).contains decl then throwError "silmaril {kind}: {decl} is already declared"
        let ty := mkApp2 (mkConst ``Silmaril.Consequence.System [Level.zero, Level.zero]) Ax C
        addConsequenceDef decl (← mkExpectedTypeHint v ty)
        fs ← fs.push kind "decl" (.str decl.toString)
        pure (decl, Ax, C)
    -- `term`: the defining constant as an instance argument prints it (a name whose first
    -- component is a keyword, such as `silmaril`, prints escaped: `«silmaril».x`)
    fs ← fs.push kind "term" (.str (← ppOneLine (mkConst d)))
    fs ← fs.push kind "contexts" (.str (← ppOneLine Ax))
    fs ← fs.push kind "conclusions" (.str (← ppOneLine C))
    fs ← systemShapeFields kind fs Ax C
    return #[(name, fs)]

end Silmaril.Project
