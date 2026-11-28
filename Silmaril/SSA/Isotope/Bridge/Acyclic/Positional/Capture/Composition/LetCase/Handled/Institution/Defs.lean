module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms
public import Silmaril.Logic.ITree.Institution.Trace.Policy.Thms

/-! # Captured LetCase and ranked sentences as handled-trace sentences

The sentences are the existing typed LetCase equations, grammar equations
and ranked equations of the captured comparison, at the finite structural
signature. Each is read as a directed sentence, left below right. The
models are the existing handled-trace models over the free request
signature: a state type, initial states and a reply policy. A directed
sentence holds when the existing trace-refinement sentence between the two
free trees holds in every environment of the bound context.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.Institution (Room)
open Silmaril.Logic.ITree (Model)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open Silmaril.Isotope.Institution.Acyclic.Captured (GrammarEquation RankedEquation grammarCase readGrammar)
open Region (packedExitType)
open Reverse (CheckedTable Program)
open Isotope.Semantics (BoundEnv)
open LetCase.Structural.Finite (Context)
open Free (Events Val model history)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- The finite structural signature as an instruction signature of the
existing equational institutions. Every primitive is effectful. -/
abbrev sig (Φ : Type) [LetCase.Structural.Finite.Signature Φ] : InstrSig (Ty Empty) Bool := ⟨Φ⟩

/-- The free requests as a signature of the handled-trace institution. -/
abbrev events (Φ : Type) [LetCase.Structural.Finite.Signature Φ] : TraceSignature.{0} := ⟨⟨Events Φ⟩⟩

/-- Handled-trace models over the free requests, with states in `Type`. -/
abbrev HandledModel (Φ : Type) [LetCase.Structural.Finite.Signature Φ] :=
  Model.{0, 0} (events Φ).toSignature

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-- The existing trace-refinement sentence between two free trees: every
finite observation of the first operand is an observation of the second. -/
noncomputable def refinement {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B)
    (ρ : BoundEnv Val γ) : Logic.ITree.TraceInstitution.Sentence.{0, 1} (events Φ) :=
  ⟨Val B, a.2.denote Val (model Φ) (fun x => x.elim) ρ, HasTrace (b.2.denote Val (model Φ) (fun x => x.elim) ρ)⟩

/-- A typed LetCase equation read from left to right holds in a handled
model when its refinement sentence holds in every environment. -/
def SatLe (M : HandledModel Φ) (e : CaseEquation (sig Φ)) : Prop :=
  ∀ ρ : BoundEnv Val e.1.bound, Logic.ITree.TraceInstitution.Sat M (refinement e.2.1 e.2.2 ρ)

/-- The same typed equation read from right to left. -/
def swap (e : CaseEquation (sig Φ)) : CaseEquation (sig Φ) := ⟨e.1, e.2.2, e.2.1⟩

variable {d : Nat} {β : Context d} {A B : Ty Empty} {I J : LCtx (Ty Empty)}

/-- A pair of captured operands as an existing typed LetCase equation. -/
def captured (a b : Operand Φ (β.snoc A) B) : CaseEquation (sig Φ) :=
  ⟨⟨d + 1, β.snoc A, B⟩, a, b⟩

/-- A pair of written checked graphs as an existing ranked equation, with
both entries at the first row. -/
def rankedOf (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) : RankedEquation (sig Φ) :=
  ⟨⟨d + 1, β.snoc (packedExitType I), J⟩, ⟨p.size, p.table, p.checked, 0, p.entry⟩,
    ⟨q.size, q.table, q.checked, 0, q.entry⟩⟩

/-- The grammar witnesses that the checked readback builds from a pair of
captured operands with a nonempty ordered interface. -/
def grammarOf (h : J ≠ []) (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)) :
    GrammarEquation (sig Φ) :=
  ⟨⟨d + 1, β.snoc (packedExitType I), J⟩, Program.ofCode h (Code.ofLetCase a.2),
    Program.ofCode h (Code.ofLetCase b.2)⟩

/-- A model can replay every complete history from an initial state. -/
def Exposing (M : HandledModel Φ) : Prop :=
  ∀ {X : Type 1} (log : Log Empty Φ) (result : X), ∃ x, M.initial x ∧ Replay M.step x (history log result)

/-- Directed LetCase sentences over handled-trace models. -/
noncomputable def caseRoom (Φ : Type) [LetCase.Structural.Finite.Signature Φ] : Room.{0, 1, 1} where
  Sen := CaseEquation (sig Φ)
  Mod := Cat.of (Discrete (HandledModel Φ))
  Sat M e := SatLe M.as e

/-- Directed grammar sentences, through the existing rendering to LetCase. -/
noncomputable def grammarRoom (Φ : Type) [LetCase.Structural.Finite.Signature Φ] : Room.{0, 1, 1} where
  Sen := GrammarEquation (sig Φ)
  Mod := Cat.of (Discrete (HandledModel Φ))
  Sat M e := SatLe M.as (grammarCase e)

/-- Directed ranked sentences, through the existing emission to grammar
witnesses and their rendering to LetCase. -/
noncomputable def rankedRoom (Φ : Type) [LetCase.Structural.Finite.Signature Φ] : Room.{0, 1, 1} where
  Sen := RankedEquation (sig Φ)
  Mod := Cat.of (Discrete (HandledModel Φ))
  Sat M e := SatLe M.as (grammarCase (readGrammar e))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
