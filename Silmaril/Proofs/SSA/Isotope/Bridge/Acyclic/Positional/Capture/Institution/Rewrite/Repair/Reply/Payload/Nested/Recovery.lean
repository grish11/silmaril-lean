module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Nested.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested

/-- The emit effects ends at the first return or request. -/
private def splitEmits {R : Type} : Reply.Normal R → List Bool × Reply.Normal R
  | .emit b rest =>
    let (effects, tail) := splitEmits rest
    (b :: effects, tail)
  | tree => ([], tree)

private theorem splitEmits_foldr {R : Type} (es : List Bool) (tree : Reply.Normal R)
    (ht : splitEmits tree = ([], tree)) :
    splitEmits (es.foldr Reply.Normal.emit tree) = (es, tree) := by
  induction es with
  | nil => exact ht
  | cons _ _ ih => simp only [List.foldr_cons, splitEmits, ih]

private theorem split_finish {L : List Sorts} (a : ArmNormal L) (b : Bool) :
    splitEmits (a.traceTree b) = (a.emits, .ret (a.result b)) :=
  splitEmits_foldr a.emits _ rfl

private theorem split_request {L : List Sorts} (es : List Bool) (req : Bool)
    (l r : InnerNormal L) (b : Bool) :
    splitEmits ((OuterNormal.request es req l r).traceTree b) =
      (es, requestTree req (l.traceTree b) (r.traceTree b)) :=
  splitEmits_foldr es _ rfl

private theorem inner_inj {L : List Sorts} (p q : InnerNormal L)
    (h₀ : ∀ b, p.traceTree false b = q.traceTree false b)
    (h₁ : ∀ b, p.traceTree true b = q.traceTree true b) : p = q := by
  have low := p.whenFalse.traceTree_inj q.whenFalse (h₀ false) (h₁ false)
  have high := p.whenTrue.traceTree_inj q.whenTrue (h₀ true) (h₁ true)
  cases p
  cases q
  cases low
  cases high
  rfl

private theorem outer_inj {L : List Sorts} (p q : OuterNormal L)
    (h₀ : p.traceTree false = q.traceTree false) (h₁ : p.traceTree true = q.traceTree true) :
    p = q := by
  cases p with
  | finish p =>
    cases q with
    | finish q => exact congrArg OuterNormal.finish (p.traceTree_inj q h₀ h₁)
    | request es req l r =>
      have prefixes := congrArg splitEmits h₀
      rw [show (OuterNormal.finish p).traceTree false = p.traceTree false from rfl,
        split_finish, split_request] at prefixes
      cases (Prod.mk.inj prefixes).2
  | request es req l r =>
    cases q with
    | finish q =>
      have prefixes := congrArg splitEmits h₀
      rw [show (OuterNormal.finish q).traceTree false = q.traceTree false from rfl,
        split_finish, split_request] at prefixes
      cases (Prod.mk.inj prefixes).2
    | request es' req' l' r' =>
      have prefixes₀ := congrArg splitEmits h₀
      have prefixes₁ := congrArg splitEmits h₁
      rw [split_request, split_request] at prefixes₀ prefixes₁
      obtain ⟨emits, rest₀⟩ := Prod.mk.inj prefixes₀
      obtain ⟨request, l₀, r₀⟩ := requestTree_inj rest₀
      obtain ⟨_, l₁, r₁⟩ := requestTree_inj (Prod.mk.inj prefixes₁).2
      rw [emits, request, inner_inj l l' l₀ l₁, inner_inj r r' r₀ r₁]

theorem outcomes_injective_proof (L : List Sorts) : Function.Injective (@Normal.outcomes L) := by
  intro p q h
  have tracks : p.traceTree = q.traceTree :=
    Reply.Normal.outcomesWith_injective _ (Exits.Exit.packed_injective L) h
  obtain ⟨request, left, right⟩ := requestTree_inj tracks
  have lhs := outer_inj p.left q.left (left false) (left true)
  have rhs := outer_inj p.right q.right (right false) (right true)
  cases p
  cases q
  cases request
  cases lhs
  cases rhs
  rfl

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested
