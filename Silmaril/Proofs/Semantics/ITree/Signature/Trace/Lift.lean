module

public import Silmaril.Semantics.ITree.Signature.Trace.Defs
import Silmaril.Proofs.Semantics.ITree.Signature.Trace.Order

public section

namespace Silmaril.Elgot.ITree.Signature.Proofs

open CategoryTheory

universe u v w

variable {S T U : Signature.{u}} {A : Type v} {X : Type w}

theorem traceLift_id (p q : Trace S.Event A) : (𝟙 S : S ⟶ S).TraceLift p q ↔ p = q := by
  constructor
  · intro lift
    induction lift with
    | «prefix» | result | request => rfl
    | exchange e r _ ih => exact congrArg (Trace.exchange e r) ih
  · rintro rfl
    induction p with
    | «prefix» => exact .prefix
    | result a => exact .result a
    | request e => exact .request e
    | exchange e r p ih => exact .exchange e r ih

private theorem traceLift_compose (f : S ⟶ T) (g : T ⟶ U)
    {p : Trace S.Event A} {q q' : Trace T.Event A} {r : Trace U.Event A}
    (first : f.TraceLift p q) (second : g.TraceLift q' r) (same : q = q') :
    (f ≫ g).TraceLift p r := by
  induction first generalizing q' r with
  | «prefix» | result =>
    cases second <;> cases same
    first | exact .prefix | exact .result _
  | @request R e =>
    cases second with
    | request e' =>
      cases same
      exact .request e
    | «prefix» | result | exchange => cases same
  | @exchange R e reply p q _ ih =>
    cases second with
    | exchange e' reply' tail =>
      cases same
      exact .exchange e reply' (ih tail rfl)
    | «prefix» | result | request => cases same

theorem traceLift_comp (f : S ⟶ T) (g : T ⟶ U) (p : Trace S.Event A) (r : Trace U.Event A) :
    (f ≫ g).TraceLift p r ↔ ∃ q, f.TraceLift p q ∧ g.TraceLift q r := by
  constructor
  · intro lift
    induction lift with
    | «prefix» => exact ⟨.prefix, .prefix, .prefix⟩
    | result a => exact ⟨.result a, .result a, .result a⟩
    | request e => exact ⟨_, .request e, .request _⟩
    | @exchange R e reply p r _ ih =>
      obtain ⟨q, first, second⟩ := ih
      let key := f.request ⟨R, e⟩
      exact ⟨.exchange key.2 (g.reply key reply) q, .exchange e (g.reply key reply) first,
        .exchange key.2 reply second⟩
  · rintro ⟨q, first, second⟩
    exact traceLift_compose f g first second rfl

theorem traceLift_unique (f : S ⟶ T) (keys : Function.Injective f.request)
    {p q : Trace S.Event A} {r s : Trace T.Event A} (h : f.TraceLift p r) (g : f.TraceLift q s)
    (equal : r = s) : p = q := by
  induction h generalizing q s with
  | «prefix» | result =>
    cases g <;> cases equal
    rfl
  | @request R event =>
    cases g with
    | @request R' event' =>
      have mapped := Option.some.inj (congrArg (fun
        | .request e => some (⟨_, e⟩ : Request T.Event)
        | _ => none) equal)
      exact congrArg (fun q : Request S.Event => Trace.request q.2) (keys mapped)
    | «prefix» | result | exchange => cases equal
  | @exchange R event reply p r tail ih =>
    cases g with
    | @exchange R' event' reply' q s tail' =>
      have parts := Option.some.inj (congrArg (fun
        | .exchange e reply rest =>
          some (⟨⟨_, e⟩, reply, rest⟩ : (q : Request T.Event) × (q.1 × Trace T.Event A))
        | _ => none) equal)
      have requests : (⟨R, event⟩ : Request S.Event) = ⟨R', event'⟩ := keys (congrArg Sigma.fst parts)
      cases requests
      have same := eq_of_heq (Sigma.mk.inj_iff.mp parts).2
      exact congrArg₂ (Trace.exchange event) (congrArg (f.reply ⟨R, event⟩) (congrArg Prod.fst same))
        (ih tail' (congrArg Prod.snd same))
    | «prefix» | result | request => cases equal

private theorem out_translate (f : S ⟶ T) (t : Tree S.Event A)
    (node : Visible S.Event A (Tree S.Event A)) (h : out t = Part.some node) :
    out (f.tree id t) = Part.some (f.visible id (f.tree id) node) := by
  rw [f.out_tree, h, Part.map_some]

/-- The witnesses from the reduct select a whole target path, keeping the
same handler states at every completed exchange. -/
theorem handledTrace_lift (f : S ⟶ T) (step : Handler X T.Event)
    (x : X) (t : Tree S.Event A) (p : Trace S.Event A)
    (handled : HandledTrace (f.restrict step) x t p) :
    ∃ q, f.TraceLift p q ∧ HandledTrace step x (f.tree id t) q := by
  induction p generalizing x t with
  | «prefix» => exact ⟨.prefix, .prefix, trivial, trivial⟩
  | result a => exact ⟨.result a, .result a, out_translate f t (.ret a) handled.1, trivial⟩
  | @request R e =>
    obtain ⟨⟨k, hk⟩, _⟩ := handled
    exact ⟨_, .request e, ⟨_, out_translate f t (.vis e k) hk⟩, trivial⟩
  | @exchange R e r p ih =>
    obtain ⟨⟨k, hk, ht⟩, y, ⟨r', hr, hs⟩, hp⟩ := handled
    let q : Request S.Event := ⟨R, e⟩
    change f.reply q r' = r at hr
    subst r
    obtain ⟨target, related, ht', hp'⟩ := ih y (k (f.reply q r')) ⟨ht, hp⟩
    exact ⟨_, .exchange e r' related, ⟨_, out_translate f t (.vis e k) hk, ht'⟩, y, hs, hp'⟩

/-- A target execution projects through the same reduct, keeping its ordered
result and its pending request, if any. -/
theorem handledTrace_project (f : S ⟶ T) (step : Handler X T.Event) (x : X) (t : Tree S.Event A)
    (p : Trace T.Event A) (handled : HandledTrace step x (f.tree id t) p) :
    ∃ q, f.TraceLift q p ∧ HandledTrace (f.restrict step) x t q := by
  induction p generalizing x t with
  | «prefix» => exact ⟨.prefix, .prefix, trivial, trivial⟩
  | result a =>
    obtain ⟨node, hn, equal⟩ := out_source f t (.ret a) handled.1
    cases node <;> cases equal
    exact ⟨.result _, .result _, hn, trivial⟩
  | @request R e =>
    obtain ⟨⟨k, hk⟩, _⟩ := handled
    obtain ⟨node, hn, equal⟩ := out_source f t (.vis e k) hk
    cases node with
    | ret => cases equal
    | vis e' k' =>
      cases equal
      exact ⟨.request e', .request e', ⟨k', hn⟩, trivial⟩
  | @exchange R e r p ih =>
    obtain ⟨⟨k, hk, ht⟩, y, hy, hp⟩ := handled
    obtain ⟨node, hn, equal⟩ := out_source f t (.vis e k) hk
    cases node with
    | ret => cases equal
    | @vis R' e' k' =>
      cases equal
      let q : Request S.Event := ⟨R', e'⟩
      obtain ⟨tail, related, ht', hp'⟩ := ih y (k' (f.reply q r)) ⟨ht, hp⟩
      exact ⟨_, .exchange e' r related, ⟨k', hn, ht'⟩, y, ⟨r, rfl, hy⟩, hp'⟩

end Silmaril.Elgot.ITree.Signature.Proofs
