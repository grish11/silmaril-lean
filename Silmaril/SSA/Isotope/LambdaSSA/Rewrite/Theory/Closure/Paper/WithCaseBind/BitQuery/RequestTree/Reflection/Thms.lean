module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReflection

/-! # Recover the structural key and separate unequal packed request trees -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Every selected subtree completes along at least one admitted history. -/
theorem outcomes_nonempty {n : Nat} (t : Tree n) (env : Assignment n) : (t.outcomes env).Nonempty :=
  BitQueryTreeReflection.outcomes_nonempty t env

/-- Strip the event that records this label, query, tag and payload. The
derivative enters exactly the selected child with that payload in scope. -/
theorem derivative {n : Nat} (env : Assignment n) (label : Bool) (query : Expr n)
    (l r : Tree (n + 1)) (reply : Reply) :
    {obs : Observation | (obs.1, FreeMonoid.of (event label (query.eval env) reply) * obs.2) ∈
        (Tree.ask label query l r).outcomes env} =
      if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2) :=
  BitQueryTreeReflection.derivative env label query l r reply

/-- Each of the four recorded replies has a nonempty derivative. -/
theorem derivative_nonempty {n : Nat} (env : Assignment n) (label : Bool) (query : Expr n)
    (l r : Tree (n + 1)) (reply : Reply) :
    {obs : Observation | (obs.1, FreeMonoid.of (event label (query.eval env) reply) * obs.2) ∈
      (Tree.ask label query l r).outcomes env}.Nonempty := by
  rw [derivative]
  cases reply.1
  · exact outcomes_nonempty l (env.push reply.2)
  · exact outcomes_nonempty r (env.push reply.2)

/-- At every continuation, the assignment tail and the next admitted
payload together exhaust the rows of its structural key. -/
theorem key_of_outcomes {n : Nat} (t u : Tree n)
    (same : ∀ env, t.outcomes env = u.outcomes env) : t.key = u.key :=
  BitQueryTreeReflection.key_of_outcomes t u same

/-- The two caller guards exhaust the single open input. -/
theorem key_of_observations (t u : Tree 1) (same : ∀ guard, t.observations guard = u.observations guard) :
    t.key = u.key :=
  BitQueryTreeReflection.key_of_observations t u same

theorem packed_eq_iff_key (t u : Tree 1) : t.packed = u.packed ↔ t.key = u.key :=
  BitQueryTreeReflection.packed_eq_iff_key t u

theorem packed_eq_iff_observations (t u : Tree 1) :
    t.packed = u.packed ↔ ∀ guard, t.observations guard = u.observations guard :=
  BitQueryTreeReflection.packed_eq_iff_observations t u

/-- The executable finite histories encode exactly the achievable outcomes
at a fixed input assignment. -/
theorem outcomes_history_iff {n : Nat} (t : Tree n) (env : Assignment n) (obs : Observation) :
    obs ∈ t.outcomes env ↔ ∃ h ∈ t.histories env, h.observation = obs :=
  BitQueryTreeReflection.outcomes_history_iff t env obs

/-- At one guard the reachable histories characterize that guard's observations. -/
theorem guard_histories_iff_observations (p q : Tree 1) (g : Bool) :
    (∀ h, h ∈ p.histories (fun _ => g) ↔ h ∈ q.histories (fun _ => g)) ↔
      p.observations g = q.observations g :=
  BitQueryTreeReflection.guard_histories_iff_observations p q g

/-- Every executable witness separates the original packed arrows at its guard. -/
theorem separate_some (p q : Tree 1) {w : Difference} (found : p.separate? q = some w) :
    w.history.observation ∈ (w.source p q).observations w.guard ∧
    w.history.observation ∉ (w.target p q).observations w.guard :=
  BitQueryTreeReflection.separate_some p q found

theorem separate_none_iff_packed (p q : Tree 1) : p.separate? q = none ↔ p.packed = q.packed :=
  BitQueryTreeReflection.separate_none_iff_packed p q

theorem separate_of_key_ne (p q : Tree 1) (different : p.key ≠ q.key) :
    ∃ w, p.separate? q = some w ∧
      w.history.observation ∈ (w.source p q).observations w.guard ∧
      w.history.observation ∉ (w.target p q).observations w.guard :=
  BitQueryTreeReflection.separate_of_key_ne p q different

/-- A completed right reply after the common request witnesses the missing
return when the deeper continuation issues another request. -/
theorem shape_search :
    Example.shorter.separate? Example.deeper =
      some ⟨false, false, ⟨[event false false (true, false)], true, false⟩⟩ :=
  BitQueryTreeReflection.shape_search

theorem depth_ne : Example.shorter.packed ≠ Example.deeper.packed :=
  BitQueryTreeReflection.depth_ne

/-- Search preserves the first two exact replies and returns a witness for
the late query on the true guard. The false guard agrees on all replies. -/
theorem late_search :
    (Example.program false).separate? (Example.program true) =
      some ⟨true, false,
        ⟨[event false true (true, true), event true true (true, false), event false true (false, false)],
          false, false⟩⟩ :=
  BitQueryTreeReflection.late_search

theorem late_false_agreement : (Example.program false).observations false = (Example.program true).observations false :=
  BitQueryTreeReflection.late_false_agreement

theorem late_key_ne : (Example.program false).key ≠ (Example.program true).key :=
  BitQueryTreeReflection.late_key_ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
