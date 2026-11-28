module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.CfgEta.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs
public import Silmaril.Semantics.NondeterministicTrace.Thms

/-! # An opt-in selected request with an observable Bit query -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery

open Silmaril.Isotope
open _root_.Silmaril.Isotope.Institution
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open LambdaSSA.Semantics.Categorical
open CategoryTheory
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

inductive Op where
  | ask (label : Bool)

def signature : InstrSig (Ty Empty) Bool where
  Instr := Op
  hasTy := ⟨fun _ => Bit, fun _ => Answer⟩
  hasEff := ⟨fun _ => true⟩

instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
instance : HasEff signature.Instr Bool := signature.hasEff

/-- An event records the request label, the supplied Bit and both reply fields. -/
structure Event where
  label : Bool
  query : Bool
  right : Bool
  payload : Bool

abbrev Trace := Tagged (FreeMonoid Event) Bool

def queryBit : value Bit → Bool
  | .inl _ => false
  | .inr _ => true

/-- Both query values have the same four possible replies. The event records
the argument of the actual primitive invocation. -/
def request (label : Bool) (q : value Bit) : Trace (value Answer) :=
  Tagged.ofOutcomes (Set.range fun reply : Bool × Bool =>
    (.ok (answer reply.1 reply.2), FreeMonoid.of ⟨label, queryBit q, reply.1, reply.2⟩))

def model : Isotope.Semantics.InstructionModel value signature.Instr Trace where
  eval
    | .ask label => request label

abbrev Seed := WithCaseBind.JoinedStep
  (WithPairReturns.JoinedStep (τ := Ty Empty) (Φ := signature.Instr) false)

theorem model_respectsPure : Isotope.Semantics.InstructionModel.RespectsPure (ε := Bool) model := by
  intro f h
  cases f; cases h

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

theorem modelCoherent :
    letI := Kleisli.instructions model
    RegionTypingCoherent (Φ := signature.Instr) J M :=
  Kleisli.regionCoherent model model_respectsPure (Tagged.ofOutcomes ∅)

/-- The standard trace Kleisli interpretation descends along this opt-in seed. -/
noncomputable def denote :=
  letI := Kleisli.instructions model
  letI : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent
  Extension.Singleton.denoteFunctor (Seed := Seed) J M (fun _ _ => ⟨rfl, rfl⟩)
    (WithCaseBind.joined_seedDenotes J M (WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false))

abbrev Exits : List (Ty Empty) := [Bit, Bit]

def constructorBit (right : Bool) (payload : Tm signature.Instr) : Tm signature.Instr :=
  if right then .inr payload else .inl payload

/-- The reply tag selects an ordered exit and its payload is returned unchanged. -/
def call (label : Bool) (argument : Tm signature.Instr) : Region signature.Instr :=
  .case (.op (.ask label) argument) (.br 0 (.var 0)) (.br 1 (.var 0))

theorem call_typed {Γ : VCtx (Ty Empty)} {argument : Tm signature.Instr}
    (label : Bool) (h : Tm.HasType Γ argument Bit) : ValueBranches Γ (call label argument) Exits :=
  .case (.op h) (.br rfl (.var (i := 0) rfl)) (.br rfl (.var (i := 0) rfl))

inductive Spelling where
  | retainedAlias
  | literal
  | wrongLiteral

/-- The guard inspects the original Bit. An alias reads that retained Bit below
the unit payload binder. The wrong spelling changes only the left-path query. -/
def arm (label : Bool) (right : Bool) : Spelling → Region signature.Instr
  | .retainedAlias => .let₁ (.var 1) (call label (.var 0))
  | .literal => call label (constructorBit right .unit)
  | .wrongLiteral => call label (constructorBit true .unit)

theorem constructorBit_value {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr}
    (right : Bool) (h : Tm.BranchValue Γ a Ty.unit) :
    Tm.BranchValue Γ (constructorBit right a) Bit := by
  cases right
  · exact .inl h
  · exact .inr h

theorem arm_typed (label right : Bool) (s : Spelling) :
    ValueBranches [Ty.unit, Bit] (arm label right s) Exits :=
  match s with
  | .retainedAlias => .let₁ (.var (i := 1) rfl)
      (call_typed label (.var (i := 0) rfl))
  | .literal => call_typed label (constructorBit_value right .unit).hasType
  | .wrongLiteral => call_typed label (constructorBit_value true .unit).hasType

def selected (label : Bool) (s : Spelling) : Region signature.Instr :=
  .case (.var 0) (arm label false s) (arm label true s)

theorem selected_typed (label : Bool) (s : Spelling) :
    ValueBranches [Bit] (selected label s) Exits :=
  .case (.var (i := 0) rfl) (arm_typed label false s) (arm_typed label true s)

/-- The actual singleton arrow packs the two original ordered exits. -/
def packed (label : Bool) (s : Spelling) :=
  Extension.Singleton.ofRegion Seed (selected_typed label s).packExits

/-- Pack the reply payload at exit zero or one according to its original tag. -/
def atExit : value Answer → value (packedExitType Exits)
  | .inl a => .inl a
  | .inr b => .inr (.inl b)

def Spelling.query : Spelling → value Bit → value Bit
  | .wrongLiteral, _ => bit true
  | _, input => input

/-- Observe the interpretation of an actual packed quotient arrow. -/
noncomputable def observations (label : Bool) (s : Spelling) (input : value Bit) :=
  ((denote.map (packed label s)).of input).outcomes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery
