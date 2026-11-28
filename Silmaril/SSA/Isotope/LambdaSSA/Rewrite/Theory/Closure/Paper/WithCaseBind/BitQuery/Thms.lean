module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedBitQuery

/-! # Native replay and trace separation for selected Bit queries -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The retained guard alias and the branch-specific literal have the same
native arrow at the original packed interface. -/
theorem packed_replay (label : Bool) : packed label .retainedAlias = packed label .literal :=
  SelectedBitQuery.packed_replay label

/-- The query field is observable for each reply under the fixed reply policy. -/
theorem request_outcome_iff (label q right payload : Bool) (q' : value Bit) :
    (Except.ok (answer right payload), FreeMonoid.of (⟨label, q, right, payload⟩ : Event))
      ∈ (request label q').outcomes ↔ q' = bit q :=
  SelectedBitQuery.request_outcome_iff label q right payload q'

/-- The actual packed interpretation records one request and preserves the
reply payload and its ordered exit. -/
theorem packed_outcomes (label : Bool) (s : Spelling) (input : value Bit) :
    observations label s input =
      Set.range fun reply : Bool × Bool =>
        (.ok (atExit (answer reply.1 reply.2)),
          FreeMonoid.of ⟨label, queryBit (s.query input), reply.1, reply.2⟩) :=
  SelectedBitQuery.packed_outcomes label s input

/-- At false input, the same request label and right-hand false reply yield
an observation with the original query that the wrong arrow cannot produce. -/
theorem wrong_literal_witness (label : Bool) :
    let observation := (Except.ok (atExit (answer true false)),
      FreeMonoid.of (⟨label, false, true, false⟩ : Event))
    observation ∈ observations label .retainedAlias (bit false) ∧
      observation ∉ observations label .wrongLiteral (bit false) :=
  SelectedBitQuery.wrong_literal_witness label

/-- The trace witness separates the original arrows in the sound opt-in quotient. -/
theorem packed_wrong_ne (label : Bool) : packed label .retainedAlias ≠ packed label .wrongLiteral :=
  SelectedBitQuery.packed_wrong_ne label

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery
