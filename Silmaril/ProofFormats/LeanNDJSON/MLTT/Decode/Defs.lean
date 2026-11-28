module

public import Silmaril.Formats.LeanNDJSON.Validate.Defs
public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Signature.Defs

public section

/-!
# Declaration events from lean4export 3.1.0

The first `signatureSize` declarations supply symbols and definitions. Later
definitions and theorem records are independent typing queries over that signature.
The importer validates table references with the existing codec, then resolves
constant references by structured Lean name against the available prefix.

The source fragment has monomorphic safe declarations, positive sorts with
closed successor/max levels, bound variables, constants, application, lambda and
Π. Binder annotations for elaboration and reduction hints do not affect the MLTT
translation. Unsupported syntax reached from a type or value is rejected. Unused
table entries carry no typing obligation.
-/

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open Silmaril.Formats.LeanNDJSON Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Failures of format validation or translation into the supported syntax. -/
inductive ImportError where
  | decode (error : DecodeError)
  | invalidReferences (line : Nat) (reason : String)
  | badSignatureSize (requested available : Nat)
  | anonymousDeclaration
  | duplicateDeclaration (name : Lean.Name)
  | unsupportedDeclaration (name : Lean.Name) (reason : String)
  | unsupportedBlock
  | unresolvedConstant (expr : Nat) (name : Lean.Name)
  | looseBVar (expr index depth : Nat)
  | unsupportedExpr (expr : Nat) (reason : String)
  | unsupportedLevel (level : Nat) (reason : String)
  | missingEntry (table : Table) (id : Nat)
  | expansionLimit (expr : Nat)
  deriving DecidableEq, Repr

/-- The structurally imported signature and subsequent events. Typing is
expressed separately by `Signature.WellTyped` and `Sentence.Valid`. -/
structure Imported where
  signature : Signature Lean.Name
  sentences : List (Sentence signature)

private structure Tables where
  names : Array Lean.Name := #[.anonymous]
  levels : Array (Except ImportError Nat) := #[.ok 0]
  exprs : Array ExprNode := #[]

private def tableEntry {α : Type} (table : Table) (entries : Array α) (id : Nat) :
    Except ImportError α :=
  match entries[id]? with
  | some a => .ok a
  | none => .error (.missingEntry table id)

private def Tables.name (t : Tables) (i : Nat) : Except ImportError Lean.Name :=
  tableEntry .name t.names i

private def Tables.level (t : Tables) (i : Nat) : Except ImportError Nat := do
  (← tableEntry .level t.levels i)

private def Tables.addLevel (t : Tables) (i : Nat) : LevelNode → Except ImportError Nat
  | .succ l => Nat.succ <$> t.level l
  | .max l r => return max (← t.level l) (← t.level r)
  | .imax .. => .error (.unsupportedLevel i "imax")
  | .param .. => .error (.unsupportedLevel i "universe parameter")

private def Tables.ofEvents (events : List Event) : Except ImportError Tables := do
  let mut t : Tables := {}
  for e in events do
    match e with
    | .name _ (.str p s) => t := { t with names := t.names.push (.str (← t.name p) s) }
    | .name _ (.num p n) => t := { t with names := t.names.push (.num (← t.name p) n) }
    | .level i l => t := { t with levels := t.levels.push (t.addLevel i l) }
    | .expr _ x => t := { t with exprs := t.exprs.push x }
    | .declaration _ => pure ()
  return t

private abbrev ImportM := ExceptT ImportError (StateM Nat)

private def spend (e : Nat) : ImportM Unit := do
  let remaining ← get
  if remaining = 0 then throw (.expansionLimit e)
  set (remaining - 1)

private def translate (t : Tables) (S : Signature Lean.Name) :
    (fuel : Nat) → (depth id : Nat) → ImportM (ETm depth)
  | 0, _, id => throw (.expansionLimit id)
  | fuel + 1, depth, id => do
    spend id
    match ← tableEntry .expr t.exprs id with
    | .bvar i =>
      if hi : i < depth then pure (.bv ⟨i, hi⟩) else throw (.looseBVar id i depth)
    | .sort l =>
      match ← t.level l with
      | 0 => throw (.unsupportedExpr id "Prop (sort 0)")
      | n + 1 => pure (.univ n)
    | .const n ls =>
      unless ls.isEmpty do throw (.unsupportedExpr id "constant with universe arguments")
      let name ← t.name n
      match S.resolve? name with
      | none => throw (.unresolvedConstant id name)
      | some i => pure (.fv (Signature.symbolSlot i))
    | .app f a => return .app (← translate t S fuel depth f) (← translate t S fuel depth a)
    | .lam _ a b _ =>
      return .abs (← translate t S fuel depth a) (← translate t S fuel (depth + 1) b)
    | .forallE _ a b _ =>
      return .pi (← translate t S fuel depth a) (← translate t S fuel (depth + 1) b)
    | .letE .. => throw (.unsupportedExpr id "let")
    | .proj .. => throw (.unsupportedExpr id "projection")
    | .natVal .. => throw (.unsupportedExpr id "natural literal")
    | .strVal .. => throw (.unsupportedExpr id "string literal")

private def readDecl (t : Tables) (S : Signature Lean.Name) (isSignature : Bool)
    (d : Declaration) : ImportM (NamedDecl Lean.Name) := do
  let (n, params, type, value, all) ← match d with
    | .axiomCode n ps a false =>
      if isSignature then pure (n, ps, a, none, []) else
        throw (.unsupportedDeclaration (← t.name n) "a sentence requires a value")
    | .definitionCode n ps a v _ .safeCode all => pure (n, ps, a, some v, all)
    | .theoremCode n ps a v all =>
      if isSignature then throw (.unsupportedDeclaration (← t.name n) "theorem in signature")
      else pure (n, ps, a, some v, all)
    | .axiomCode n .. | .definitionCode n .. =>
      throw (.unsupportedDeclaration (← t.name n) "unsafe or partial declaration")
    | .opaqueCode n .. => throw (.unsupportedDeclaration (← t.name n) "opaque")
    | .quot n .. => throw (.unsupportedDeclaration (← t.name n) "quotient")
    | .inductive .. => throw .unsupportedBlock
  let name ← t.name n
  if name == .anonymous then throw .anonymousDeclaration
  unless params.isEmpty do throw (.unsupportedDeclaration name "universe parameters")
  let group ← all.mapM (fun i => do t.name i)
  unless group.isEmpty || group == [name] do
    throw (.unsupportedDeclaration name "mutual declaration")
  let lower := translate t S t.exprs.size 0
  return ⟨name, ← lower type, ← value.mapM lower⟩

private def validateDeclNames (t : Tables) (events : List Event) : Except ImportError Unit := do
  let mut seen : Std.HashSet Lean.Name := {}
  for n in declNames events do
    let name ← t.name n
    if name == .anonymous then throw .anonymousDeclaration
    if seen.contains name then throw (.duplicateDeclaration name)
    seen := seen.insert name

private def readDeclarations (t : Tables) (decls : List Declaration) (signatureSize : Nat) :
    ImportM Imported := do
  let mut signature : Signature Lean.Name := ⟨[]⟩
  for d in decls.take signatureSize do
    let declaration ← readDecl t signature true d
    signature := ⟨signature.declarations ++ [declaration]⟩
  let scope := signature
  let sentences ← (decls.drop signatureSize).mapM fun d => do
    let e ← readDecl t scope false d
    let some value := e.value
      | throw (.unsupportedDeclaration e.name "a sentence requires a value")
    return Sentence.atSignature scope ⟨e.name, e.type, value⟩
  return ⟨scope, sentences⟩

/-- Validate decoded records, then import the prefix and queries. The node
budget counts translated occurrences, including expansion of shared subterms. -/
def importEvents (signatureSize : Nat) (events : List Event) (nodeBudget : Nat := 100000) :
    Except ImportError Imported := do
  unless serialValid? .initial events do
    let (line, reason) := (firstInvalid 2 .initial events).getD (0, "invalid references")
    throw (.invalidReferences line reason)
  let t ← Tables.ofEvents events
  validateDeclNames t events
  let decls := events.filterMap fun | .declaration d => some d | _ => none
  unless signatureSize ≤ decls.length do throw (.badSignatureSize signatureSize decls.length)
  (readDeclarations t decls signatureSize).run.run' nodeBudget

/-- Decode actual lean4export bytes, validate references and resolve the supported fragment. -/
def importBytes (signatureSize : Nat) (bytes : List UInt8) (nodeBudget : Nat := 100000) :
    Except ImportError Imported := do
  let file ← (parseFile bytes).mapError .decode
  importEvents signatureSize file.events nodeBudget

end Silmaril.ProofFormats.LeanNDJSON.MLTT
