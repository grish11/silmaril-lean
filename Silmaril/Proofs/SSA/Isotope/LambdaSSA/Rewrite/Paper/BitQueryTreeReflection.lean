module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

/-! # Recover the selected tree from its ordered finite observations -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReflection

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)

private theorem terminal_injective {a b c d : Bool} (e : terminal a b = terminal c d) : a = c ∧ b = d := by
  cases a <;> cases c
  · refine ⟨rfl, ?_⟩
    have same : bit b = bit d := Sum.inl.inj e
    cases b <;> cases d <;> first | rfl | cases same
  · cases e
  · cases e
  · refine ⟨rfl, ?_⟩
    have same : bit b = bit d := Sum.inl.inj (Sum.inr.inj e)
    cases b <;> cases d <;> first | rfl | cases same

theorem outcomes_nonempty {n : Nat} (t : Tree n) (env : Assignment n) : (t.outcomes env).Nonempty := by
  induction t with
  | ret right i => exact ⟨(.ok (terminal right (env i)), 1), rfl⟩
  | ask label query l r ihl ihr =>
    obtain ⟨⟨result, tail⟩, hit⟩ := ihl (env.push false)
    exact ⟨(result, FreeMonoid.of (event label (query.eval env) (false, false)) * tail),
      (false, false), tail, hit, rfl⟩

theorem derivative {n : Nat} (env : Assignment n) (label : Bool) (query : Expr n)
    (l r : Tree (n + 1)) (reply : Reply) :
    {obs : Observation | (obs.1, FreeMonoid.of (event label (query.eval env) reply) * obs.2) ∈
        (Tree.ask label query l r).outcomes env} =
      if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2) := by
  apply Set.ext
  rintro ⟨result, tail⟩
  change (result, FreeMonoid.of (event label (query.eval env) reply) * tail) ∈
      (Tree.ask label query l r).outcomes env ↔
    (result, tail) ∈ (if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2))
  rw [outcome_with_head]
  exact ⟨fun h => h.2.2, fun h => ⟨rfl, rfl, h⟩⟩

private theorem ask_has_event {n : Nat} (env : Assignment n) (label : Bool) (query : Expr n)
    (l r : Tree (n + 1)) (result : Except Bool Result) :
    (result, 1) ∉ (Tree.ask label query l r).outcomes env := by
  rintro ⟨reply, tail, _, log⟩
  have impossible : event label (query.eval env) reply :: tail.toList = [] :=
    congrArg FreeMonoid.toList log
  cases impossible

private theorem ask_head_eq {n : Nat} (env : Assignment n) {label label' : Bool} {q q' : Expr n}
    {l r l' r' : Tree (n + 1)}
    (same : (Tree.ask label q l r).outcomes env = (Tree.ask label' q' l' r').outcomes env) :
    label = label' ∧ q.eval env = q'.eval env := by
  obtain ⟨⟨result, tail⟩, hit⟩ := outcomes_nonempty l (env.push false)
  let e := event label (q.eval env) (false, false)
  have left : (result, FreeMonoid.of e * tail) ∈ (Tree.ask label q l r).outcomes env :=
    ⟨(false, false), tail, hit, rfl⟩
  have fields := (outcome_with_head env label' q' l' r' e tail result).mp (same ▸ left)
  exact ⟨fields.1, fields.2.1⟩

private theorem push_tail {n : Nat} (env : Assignment (n + 1)) :
    env.tail.push (env 0) = env := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Assignment.push, Assignment.tail]

theorem key_of_outcomes {n : Nat} (t u : Tree n)
    (same : ∀ env, t.outcomes env = u.outcomes env) : t.key = u.key := by
  induction t with
  | @ret n right i =>
    cases u with
    | ret right' i' =>
      have value_at (env : Assignment n) : right = right' ∧ env i = env i' := by
        have hit : (.ok (terminal right (env i)), (1 : Word)) ∈
            (Tree.ret right' i').outcomes env := (same env) ▸ (show _ ∈ (Tree.ret right i).outcomes env from rfl)
        have eq : (Except.ok (terminal right (env i)), (1 : Word)) =
            (.ok (terminal right' (env i')), (1 : Word)) := hit
        exact terminal_injective (Except.ok.inj (congrArg Prod.fst eq))
      have tag := (value_at (fun _ => false)).1
      have slot : i = i' := by
        have selected := (value_at (fun j => decide (j = i))).2
        have target : decide (i' = i) = true := selected.symm.trans (by simp)
        exact (of_decide_eq_true target).symm
      cases tag
      cases slot
      rfl
    | ask label q l r =>
      let env : Assignment n := fun _ => false
      have hit : (.ok (terminal right (env i)), (1 : Word)) ∈
          (Tree.ask label q l r).outcomes env := (same env) ▸ (show _ ∈ (Tree.ret right i).outcomes env from rfl)
      exact (ask_has_event env label q l r _ hit).elim
  | @ask n label query l r ihl ihr =>
    cases u with
    | ret right i =>
      let env : Assignment n := fun _ => false
      have hit : (.ok (terminal right (env i)), (1 : Word)) ∈
          (Tree.ask label query l r).outcomes env :=
        (same env).symm ▸ (show _ ∈ (Tree.ret right i).outcomes env from rfl)
      exact (ask_has_event env label query l r _ hit).elim
    | ask label' query' l' r' =>
      have heads (env : Assignment n) := ask_head_eq env (same env)
      have labelEq := (heads (fun _ => false)).1
      have queryEq : query.eval = query'.eval := funext fun env => (heads env).2
      have children (env : Assignment n) (reply : Reply) :
          (if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2)) =
          (if reply.1 then r'.outcomes (env.push reply.2) else l'.outcomes (env.push reply.2)) := by
        rw [← derivative env label query l r reply, ← derivative env label' query' l' r' reply]
        rw [same env, labelEq, queryEq]
      have leftEq : l.key = l'.key := ihl l' (fun env => by
        have e := children env.tail (false, env 0)
        simpa only [push_tail, Bool.false_eq_true, ite_false] using e)
      have rightEq : r.key = r'.key := ihr r' (fun env => by
        have e := children env.tail (true, env 0)
        simpa only [push_tail, ite_true] using e)
      simp only [Tree.key, labelEq, queryEq, leftEq, rightEq]

theorem key_of_observations (t u : Tree 1) (same : ∀ g, t.observations g = u.observations g) :
    t.key = u.key := by
  apply key_of_outcomes
  intro env
  have all : env = fun _ : Fin 1 => env 0 := funext fun i => congrArg env (Fin.eq_zero i)
  rw [all, ← packed_outcomes, ← packed_outcomes]
  exact same (env 0)

theorem packed_eq_iff_key (t u : Tree 1) : t.packed = u.packed ↔ t.key = u.key := by
  constructor
  · intro eq
    apply key_of_observations
    intro g
    unfold Tree.observations
    rw [eq]
  · exact packed_eq_of_key

theorem packed_eq_iff_observations (t u : Tree 1) :
    t.packed = u.packed ↔ ∀ g, t.observations g = u.observations g := by
  constructor
  · intro eq g
    unfold Tree.observations
    rw [eq]
  · intro same
    exact packed_eq_of_key (key_of_observations t u same)

private theorem reply_mem (r : Reply) : r ∈ replies := by
  obtain ⟨tag, b⟩ := r
  cases tag <;> cases b <;> decide

private theorem history_injective : Function.Injective History.observation := by
  intro h h' eq
  have eventEq := congrArg (fun o : Observation => o.2.toList) eq
  have values := terminal_injective (Except.ok.inj (congrArg Prod.fst eq))
  cases h
  cases h'
  simp only [History.mk.injEq]
  exact ⟨eventEq, values.1, values.2⟩

theorem outcomes_history_iff {n : Nat} (t : Tree n) (env : Assignment n) (obs : Observation) :
    obs ∈ t.outcomes env ↔ ∃ h ∈ t.histories env, h.observation = obs := by
  induction t generalizing obs with
  | ret right i =>
    change obs = (⟨[], right, env i⟩ : History).observation ↔
      ∃ h ∈ ([⟨[], right, env i⟩] : List History), h.observation = obs
    simp only [List.mem_singleton]
    exact ⟨fun h => ⟨_, rfl, h.symm⟩, fun ⟨_, h, eq⟩ => h ▸ eq.symm⟩
  | ask label query l r ihl ihr =>
    have child (reply : Reply) (o : Observation) :
        o ∈ (if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2)) ↔
          ∃ h ∈ (if reply.1 then r.histories (env.push reply.2) else l.histories (env.push reply.2)),
            h.observation = o := by
      obtain ⟨tag, b⟩ := reply
      cases tag
      · exact ihl (env.push b) o
      · exact ihr (env.push b) o
    simp only [Tree.outcomes, Set.mem_ofPred_eq, Tree.histories, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨reply, tail, hit, word⟩
      obtain ⟨h, live, eq⟩ := (child reply (obs.1, tail)).mp hit
      have valueEq := congrArg (fun o : Observation => o.1) eq
      refine ⟨{ h with events := event label (query.eval env) reply :: h.events },
        ⟨reply, reply_mem reply, h, live, rfl⟩, Prod.ext valueEq ?_⟩
      have tailEq : FreeMonoid.ofList h.events = tail := congrArg Prod.snd eq
      change FreeMonoid.ofList (event label (query.eval env) reply :: h.events) = obs.2
      rw [FreeMonoid.ofList_cons, tailEq, word]
    · rintro ⟨_, ⟨reply, _, h, live, rfl⟩, rfl⟩
      exact ⟨reply, FreeMonoid.ofList h.events, (child reply _).mpr ⟨h, live, rfl⟩, rfl⟩

theorem history_in_packed_iff (p : Tree 1) (g : Bool) (h : History) :
    h ∈ p.histories (fun _ => g) ↔ h.observation ∈ p.observations g := by
  rw [packed_outcomes]
  change h ∈ p.histories (fun _ => g) ↔ h.observation ∈ p.outcomes (fun _ => g)
  rw [outcomes_history_iff]
  constructor
  · exact fun hit => ⟨h, hit, rfl⟩
  · rintro ⟨other, hit, eq⟩
    exact history_injective eq ▸ hit

theorem guard_histories_iff_observations (p q : Tree 1) (g : Bool) :
    (∀ h, h ∈ p.histories (fun _ => g) ↔ h ∈ q.histories (fun _ => g)) ↔
      p.observations g = q.observations g := by
  constructor
  · intro same
    rw [packed_outcomes, packed_outcomes]
    apply Set.ext
    intro obs
    simp only [outcomes_history_iff, same]
  · intro same h
    rw [history_in_packed_iff p g, history_in_packed_iff q g, same]

private theorem candidate_iff (p q : Tree 1) (w : Difference) :
    w ∈ p.candidates q ↔ w.history ∈ (w.source p q).histories (fun _ => w.guard) := by
  simp only [Tree.candidates, List.mem_flatMap, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨g, _, ⟨h, hit, rfl⟩ | ⟨h, hit, rfl⟩⟩
    · exact hit
    · exact hit
  · intro hit
    refine ⟨w.guard, ?_, ?_⟩
    · cases w.guard <;> decide
    · obtain ⟨g, side, h⟩ := w
      cases side
      · exact Or.inl ⟨h, hit, rfl⟩
      · exact Or.inr ⟨h, hit, rfl⟩

theorem separate_some (p q : Tree 1) {w : Difference} (found : p.separate? q = some w) :
    w.history.observation ∈ (w.source p q).observations w.guard ∧
    w.history.observation ∉ (w.target p q).observations w.guard := by
  have source := (candidate_iff p q w).mp (List.mem_of_find?_eq_some found)
  let absent (candidate : Difference) :=
    decide (candidate.history ∉ (candidate.target p q).histories (fun _ => candidate.guard))
  have target : w.history ∉ (w.target p q).histories (fun _ => w.guard) :=
    of_decide_eq_true (List.find?_some (p := absent) found)
  exact ⟨(history_in_packed_iff _ _ _).mp source, fun hit => target ((history_in_packed_iff _ _ _).mpr hit)⟩

theorem separate_none_iff_packed (p q : Tree 1) : p.separate? q = none ↔ p.packed = q.packed := by
  have exhausted : p.separate? q = none ↔
      ∀ w ∈ p.candidates q, w.history ∈ (w.target p q).histories (fun _ => w.guard) := by
    simp [Tree.separate?]
  rw [exhausted, packed_eq_iff_observations]
  constructor
  · intro all g
    apply (guard_histories_iff_observations p q g).mp
    intro h
    exact ⟨fun hit => all ⟨g, false, h⟩ ((candidate_iff p q _).mpr hit),
      fun hit => all ⟨g, true, h⟩ ((candidate_iff p q _).mpr hit)⟩
  · intro eq w hit
    have src := (history_in_packed_iff _ _ _).mp ((candidate_iff p q w).mp hit)
    apply (history_in_packed_iff _ _ _).mpr
    obtain ⟨g, side, h⟩ := w
    cases side
    · exact (eq g) ▸ src
    · exact (eq g).symm ▸ src

theorem separate_of_key_ne (p q : Tree 1) (different : p.key ≠ q.key) :
    ∃ w, p.separate? q = some w ∧
      w.history.observation ∈ (w.source p q).observations w.guard ∧
      w.history.observation ∉ (w.target p q).observations w.guard := by
  cases found : p.separate? q with
  | none => exact (different ((packed_eq_iff_key p q).mp ((separate_none_iff_packed p q).mp found))).elim
  | some w => exact ⟨w, rfl, separate_some p q found⟩

theorem shape_search :
    Example.shorter.separate? Example.deeper =
      some ⟨false, false, ⟨[event false false (true, false)], true, false⟩⟩ := by decide

theorem depth_ne : Example.shorter.packed ≠ Example.deeper.packed := by
  intro eq
  have none := (separate_none_iff_packed _ _).mpr eq
  rw [shape_search] at none
  cases none

theorem late_search :
    (Example.program false).separate? (Example.program true) =
      some ⟨true, false,
        ⟨[event false true (true, true), event true true (true, false), event false true (false, false)],
          false, false⟩⟩ := by decide

theorem late_false_agreement : (Example.program false).observations false = (Example.program true).observations false := by
  have same : (Example.program false).histories (fun _ => false) =
      (Example.program true).histories (fun _ => false) := by decide
  apply (guard_histories_iff_observations _ _ false).mp
  intro h
  rw [same]

theorem late_key_ne : (Example.program false).key ≠ (Example.program true).key :=
  fun eq => three_request_ne (packed_eq_of_key eq)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReflection
