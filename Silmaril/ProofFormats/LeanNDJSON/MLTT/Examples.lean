module

import Silmaril.ProofFormats.LeanNDJSON.MLTT.Bounded.Thms
import Silmaril.ProofFormats.LeanNDJSON.MLTT.Decode.Thms
meta import Silmaril.ProofFormats.LeanNDJSON.MLTT.Decode.Defs

/-! Regression tests for the actual exporter fixture and the MLTT interpretation. -/

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT.Examples

open Silmaril.Formats.LeanNDJSON
open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.SetTheory

private def carrierName : Lean.Name := `LeanNDJSONFixture.Carrier

private def carrierSignature : Signature Lean.Name :=
  ⟨[⟨carrierName, .univ 1, some (.univ 0)⟩]⟩

private def carrierUse : Sentence carrierSignature :=
  .atSignature carrierSignature ⟨`LeanNDJSONFixture.useCarrier, .univ 1,
    .fv (Signature.symbolSlot 0)⟩

private def carrierContext : ECtx :=
  .cons .nil (Signature.symbolSlot 0) (.univ 1)

private theorem carrierContext_ok : carrierContext.JEq .unit .star .star :=
  .cons_ok .nil_ok (by simp [ECtx.dv]) (.univ .nil_ok)

private theorem carrierSignature_wellTyped : carrierSignature.WellTyped := by
  have hv : carrierContext.JEq (.univ 1)
      (.fv (Signature.symbolSlot 0)) (.fv (Signature.symbolSlot 0)) :=
    .var carrierContext_ok (.here _ _ _)
  exact .cons_ok carrierContext_ok (by decide)
    (.id (.univ carrierContext_ok) hv (.univ carrierContext_ok))

example : carrierUse.Valid :=
  carrierUse.valid_iff.mpr
    (.var carrierSignature_wellTyped (.there _ _ _ _ _ (.here _ _ _) (by decide)))

private def universeEvent : Sentence (⟨[]⟩ : Signature String) :=
  .atSignature ⟨[]⟩ ⟨"universe", .univ 1, .univ 0⟩

example (T : FiniteTower 1) : ¬ (⟨1, T⟩ : BudgetModel).Satisfies universeEvent :=
  fun h => (by decide : ¬ 2 ≤ 1) h.1

private def universeAtTwo : BoundedSentence 2 (⟨[]⟩ : Signature String) :=
  ⟨universeEvent, show 2 ≤ 2 from Nat.le_refl _⟩

private theorem universeAtTwo_derivable : fixedDerives ∅ universeAtTwo :=
  .univ (show 0 + 1 < 2 by decide) .nil_ok

example (T : FiniteTower 2) : (⟨2, T⟩ : BudgetModel).Satisfies universeEvent :=
  BudgetModel.satisfies_of_fixed_derivation ⟨2, T⟩ universeAtTwo_derivable (fun _ h => False.elim h)

example : fixedDerives ∅ (BoundedSentence.include (by decide : 2 ≤ 3) universeAtTwo) := by
  have lifted :=
    (fixedInclusionLogic.{0} String (by decide : 2 ≤ 3)).map_derives _ ∅ _ universeAtTwo_derivable
  rw [Set.image_empty] at lifted
  exact lifted

private def selfMembership : Sentence (⟨[]⟩ : Signature String) :=
  .atSignature ⟨[]⟩ ⟨"selfMembership", .univ 0, .univ 0⟩

example (T : FiniteTower 1) : ¬ (⟨1, T⟩ : BudgetModel).Satisfies selfMembership :=
  fun h => ZFSet.mem_irrefl (T.U 0) ((h.2 (fun _ => ∅) trivial).2)

private meta def expect (what : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"Lean NDJSON MLTT regression: {what}")

private meta def reject (what : String) (out : Except ImportError Imported)
    (test : ImportError → Bool) : IO Unit :=
  expect what (match out with | .ok _ => false | .error e => test e)

-- Read the actual lean4export 3.1.0 fixture through the production byte path.
#eval do
  let bytes := (← IO.FS.readFile "tests/lean-ndjson/mltt-fragment.ndjson").toUTF8.toList
  let .ok out := importBytes 1 bytes | throw (IO.userError "fixture rejected")
  let [⟨name, .univ 1, some (.univ 0)⟩] := out.signature.declarations
    | throw (IO.userError "unexpected signature")
  expect "carrier name" (name == `LeanNDJSONFixture.Carrier)
  let [use, identity, applied] := out.sentences | throw (IO.userError "expected three queries")
  let .univ 1 := use.event.type | throw (IO.userError "unexpected useCarrier type")
  let .fv slot := use.event.value | throw (IO.userError "unexpected useCarrier value")
  expect "useCarrier refers to slot zero"
    (use.event.name == `LeanNDJSONFixture.useCarrier && slot == Signature.symbolSlot 0)
  let .pi (.univ 0) (.pi (.bv argType) (.bv resultType)) := identity.event.type
    | throw (IO.userError "unexpected dependent identity type")
  let .abs (.univ 0) (.abs (.bv param) (.bv body)) := identity.event.value
    | throw (IO.userError "unexpected identity body")
  expect "binder scope" (argType.val == 0 && resultType.val == 1 && param.val == 0 && body.val == 0)
  let .app (.abs (.univ 1) (.bv bound)) (.fv argument) := applied.event.value
    | throw (IO.userError "unexpected application")
  expect "application preserves the name and binding"
    (bound.val == 0 && argument == Signature.symbolSlot 0)
  reject "queries cannot declare constants for later queries" (importBytes 0 bytes)
    fun | .unresolvedConstant 2 name => name == `LeanNDJSONFixture.Carrier | _ => false
  reject "shared expression expansion is bounded" (importBytes 1 bytes 1)
    fun | .expansionLimit _ => true | _ => false
  reject "malformed metadata" (importBytes 1 "{}\n".toUTF8.toList)
    fun | .decode _ => true | _ => false

private def namedRecords : List Event :=
  [ .name 1 (.str 0 "A"), .name 2 (.str 1 "1"), .name 3 (.num 1 1)
  , .name 4 (.str 0 "A.1"), .name 5 (.num 1 1), .name 6 (.str 0 "query")
  , .level 1 (.succ 0), .expr 0 (.sort 1)
  , .declaration (.axiomCode 2 [] 0 false), .declaration (.axiomCode 3 [] 0 false)
  , .declaration (.axiomCode 4 [] 0 false)
  ]

private def query (type value : Nat) : Event :=
  .declaration (.definitionCode 6 [] type value .abbrev .safeCode [6])

#eval do
  let es : List Event := namedRecords ++
    [ Event.expr 1 (.const 2 []), Event.expr 2 (.const 5 []), Event.expr 3 (.const 4 [])
    , Event.expr 4 (.app 2 3), Event.expr 5 (.app 1 4), query 0 5 ]
  let .ok out := importEvents 3 es | throw (IO.userError "structured names rejected")
  let [s] := out.sentences | throw (IO.userError "expected one query")
  let .app (.fv a) (.app (.fv b) (.fv c)) := s.event.value
    | throw (IO.userError "unexpected constant translation")
  expect "string, numeric and dotted components have separate slots"
    (a == Signature.symbolSlot 0 && b == Signature.symbolSlot 1 && c == Signature.symbolSlot 2)
  reject "duplicate structured declaration name under a new table id"
    (importEvents 4 (namedRecords ++ [Event.declaration (.axiomCode 5 [] 0 false)]))
    fun | .duplicateDeclaration (.num (.str .anonymous "A") 1) => true | _ => false
  reject "forward expression id" (importEvents 3 (namedRecords ++ [query 0 1]))
    fun | .invalidReferences _ _ => true | _ => false
  reject "loose bound variable"
    (importEvents 3 (namedRecords ++ [Event.expr 1 (.bvar 0), query 0 1]))
    fun | .looseBVar 1 0 0 => true | _ => false
  reject "unsupported Prop sort"
    (importEvents 3 (namedRecords ++ [Event.expr 1 (.sort 0), query 0 1]))
    fun | .unsupportedExpr 1 "Prop (sort 0)" => true | _ => false
  reject "unsupported level expression"
    (importEvents 3 (namedRecords ++ [Event.level 2 (.imax 1 1), Event.expr 1 (.sort 2), query 0 1]))
    fun | .unsupportedLevel 2 "imax" => true | _ => false
  reject "unsupported expression in the query body"
    (importEvents 3 (namedRecords ++ [Event.expr 1 (.natVal "1"), query 0 1]))
    fun | .unsupportedExpr 1 "natural literal" => true | _ => false
  -- Structurally valid and supported syntax can still ask for an ill-typed judgment.
  let .ok out := importEvents 0 (namedRecords.take 8 ++ [query 0 0])
    | throw (IO.userError "the importer treated typing as format validation")
  let [s] := out.sentences | throw (IO.userError "expected one query")
  let (.univ 0, .univ 0) := (s.event.type, s.event.value)
    | throw (IO.userError "expected a universe to be asserted to inhabit itself")
  pure ()

end Silmaril.ProofFormats.LeanNDJSON.MLTT.Examples
