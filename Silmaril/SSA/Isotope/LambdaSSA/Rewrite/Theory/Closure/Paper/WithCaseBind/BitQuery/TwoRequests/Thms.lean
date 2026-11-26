module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.TwoRequests.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries

/-! # Canonical native replay and validated comparison of two Bit requests -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Replay the selected source to the ordered quote at its actual packed interface. -/
theorem packed_replay (p : Program) : p.packed = p.key.packed :=
  TwoBitQueries.packed_replay p

/-- Observe both labels, both query values and reply fields, and the final ordered exit. -/
theorem packed_outcomes (p : Program) (guard : Bool) :
    p.observations guard = p.key.outcomes guard :=
  TwoBitQueries.packed_outcomes p guard

/-- The labels and second-query table characterize native equality in this fragment. -/
theorem packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.key = q.key :=
  TwoBitQueries.packed_eq_iff_key p q

/-- The checked model separates distinct keys across the two possible guard inputs. -/
theorem observations_iff_packed_eq (p q : Program) :
    (∀ guard, p.observations guard = q.observations guard) ↔ p.packed = q.packed :=
  TwoBitQueries.observations_iff_packed_eq p q

/-- The compact XOR and its full ordered quote have the same original packed arrow. -/
theorem xor_quote_replay : Example.xor.packed = Example.xorQuote.packed :=
  TwoBitQueries.xor_quote_replay

/-- At the same input and reply history, both arrows keep their labels and terminal
behavior. The observed second query distinguishes the two original arrows. -/
theorem second_query_witness :
    Example.observation true ∈ Example.xor.observations true ∧
    Example.observation false ∈ Example.replyOnly.observations true ∧
    Example.observation true ∉ Example.replyOnly.observations true :=
  TwoBitQueries.second_query_witness

theorem second_query_ne : Example.xor.packed ≠ Example.replyOnly.packed :=
  TwoBitQueries.second_query_ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests
