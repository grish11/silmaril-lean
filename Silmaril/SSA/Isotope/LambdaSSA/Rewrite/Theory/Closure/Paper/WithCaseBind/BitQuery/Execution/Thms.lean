module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryExecution

/-! # Direct evaluation of selected cases and request replies -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.Execution

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open scoped MonoidalCategory

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types
local notation "U" => (Ty.unit : Ty Empty)

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

theorem case_run {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm signature.Instr}
    {l r : Region signature.Instr} {ha : Tm.HasType Γ a (coprod A B)}
    {sa : (J).obj (ctxObj M Γ) ⟶ (J).obj (value (coprod A B))}
    (d : Denotes J M ha sa) (hl : ValueBranches (A :: Γ) l Exits)
    (hr : ValueBranches (B :: Γ) r Exits) (x : ctxObj M Γ) :
    runAt (.case ha hl hr) x =
      Bind.bind (m := Trace) (sa.of x)
        (fun | .inl a => runAt hl (x, a) | .inr b => runAt hr (x, b)) :=
  BitQueryExecution.case_run d hl hr x

theorem request_case_run {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (label b : Bool) (hl : ValueBranches (Bit :: Γ) l Exits) (hr : ValueBranches (Bit :: Γ) r Exits)
    (x : ctxObj M Γ) :
    runAt (.case (.op (f := (show signature.Instr from .ask label))
      (constructorBit_value b .unit).hasType) hl hr) x =
      (request label (bit b) >>= fun | .inl a => runAt hl (x, a) | .inr a => runAt hr (x, a)) :=
  BitQueryExecution.request_case_run label b hl hr x

theorem run_packed {r : Region signature.Instr} (hr : ValueBranches [Bit] r Exits) (g : Bool) :
    (denote.map (Paper.Extension.Singleton.ofRegion Seed hr.packExits)).of (bit g) =
      runAt hr (PUnit.unit, bit g) :=
  BitQueryExecution.run_packed hr g

theorem bind_request {A : Type} (label b : Bool) (next : value Answer → Trace A)
    (result : Except Bool A) (word : FreeMonoid Event) :
    (result, word) ∈ (request label (bit b) >>= next).outcomes ↔
      ∃ (reply : Bool × Bool) (tail : FreeMonoid Event), (result, tail) ∈ (next (answer reply.1 reply.2)).outcomes ∧
        FreeMonoid.of ⟨label, b, reply.1, reply.2⟩ * tail = word :=
  BitQueryExecution.bind_request label b next result word

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.Execution
