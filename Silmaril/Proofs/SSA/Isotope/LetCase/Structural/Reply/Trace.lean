module

public import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Defs

public section

namespace Silmaril.Isotope.LetCase.Structural.Reply

open LocallyNameless (Derivation Tm)
open Silmaril.Isotope.Semantics (BoundEnv)
open LetSeq.StraightLine.Structural (Trace Log Event model)
open Silmaril.Semantics.NondeterministicTrace

local notation "Value" => LetSeq.StraightLine.Structural.Value

variable {α Φ : Type} [HasTy Φ (Ty α)]
set_option backward.isDefEq.respectTransparency false

private theorem prefix_mul (a b : Log α Φ) : a.toList <+: (a * b).toList :=
  ⟨b.toList, rfl⟩

private theorem match_prefix {A : Type} {m : Trace α Φ A} (hm : PrefixDetermined m)
    {x y : A} {a b c d : Log α Φ}
    (hx : (x, a) ∈ m.outcomes) (hy : (y, b) ∈ m.outcomes)
    (pref : (a * c).toList <+: (b * d).toList) : x = y ∧ a = b := by
  rcases List.prefix_or_prefix_of_prefix ((prefix_mul a c).trans pref) (prefix_mul b d) with h | h
  · exact hm hx hy h
  · obtain ⟨rfl, rfl⟩ := hm hy hx h
    exact ⟨rfl, rfl⟩

private theorem pure_determined {A : Type} (x : A) :
    PrefixDetermined (pure x : Trace α Φ A) := by
  intro y z u v hy hz _
  have hy' : (y, u) = (x, 1) := hy
  have hz' : (z, v) = (x, 1) := hz
  exact Prod.mk.inj (hy'.trans hz'.symm)

private theorem bind_determined {A B : Type} {m : Trace α Φ A} (hm : PrefixDetermined m)
    {k : A → Trace α Φ B} (hk : ∀ x, PrefixDetermined (k x)) : PrefixDetermined (m >>= k) := by
  intro x y u v xu yv pref
  obtain ⟨a, l, r, ha, hx, rfl⟩ := Finite.mem_bind.mp xu
  obtain ⟨b, l', r', hb, hy, rfl⟩ := Finite.mem_bind.mp yv
  obtain ⟨rfl, rfl⟩ := match_prefix hm ha hb pref
  have tail : r.toList <+: r'.toList := (List.prefix_append_right_inj l.toList).mp pref
  obtain ⟨rfl, rfl⟩ := hk a hx hy tail
  exact ⟨rfl, rfl⟩

private theorem primitive_determined (f : Φ) (a : Value (instrSrc (τ := Ty α) f)) :
    PrefixDetermined ((model (α := α)).eval f a) := by
  intro x y u v hx hy pref
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
  let first : Event (α := α) (Φ := Φ) := ⟨f, a, r⟩
  let second : Event (α := α) (Φ := Φ) := ⟨f, a, s⟩
  have singleton : [first] <+: [second] := pref
  have events : first = second := by
    obtain ⟨tail, eq⟩ := singleton
    exact (List.cons.inj eq).1
  have reply : r = s := eq_of_heq (Event.mk.inj events).2.2
  exact ⟨reply, congrArg (fun z => FreeMonoid.of (Event.mk (α := α) f a z)) reply⟩

/-- Constructor induction over the exact native syntax, including abort. -/
theorem run_prefix_determined_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm Empty Φ n} {A : Ty α} (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Value β) :
    PrefixDetermined (run d ρ) := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact pure_determined _
  | @op _ _ f _ _ ih => exact bind_determined (ih ρ) (primitive_determined f)
  | @let₁ _ _ _ _ A B a b iha ihb =>
    exact bind_determined (iha ρ) (fun x => ihb (ρ.snoc x))
  | unit => exact pure_determined _
  | pair a b iha ihb =>
    exact bind_determined (iha ρ) (fun _ => bind_determined (ihb ρ) (fun _ => pure_determined _))
  | let₂ a b iha ihb =>
    exact bind_determined (iha ρ) (fun x => ihb ((ρ.snoc x.1).snoc x.2))
  | inl a ih => exact bind_determined (ih ρ) (fun _ => pure_determined _)
  | inr a ih => exact bind_determined (ih ρ) (fun _ => pure_determined _)
  | case a l r iha ihl ihr =>
    apply bind_determined (iha ρ)
    intro x
    cases x with
    | inl x => exact ihl (ρ.snoc x)
    | inr y => exact ihr (ρ.snoc y)
  | abort a ih =>
    apply bind_determined (ih ρ)
    intro x
    exact x.elim

private theorem cancel_mem {A B : Type} {m : Trace α Φ A} (hm : PrefixDetermined m)
    {k : A → Trace α Φ B} {a : A} {l : Log α Φ} {b : B} {r : Log α Φ}
    (ha : (a, l) ∈ m.outcomes)
    (obs : (b, l * r) ∈ (m >>= k).outcomes) : (b, r) ∈ (k a).outcomes := by
  obtain ⟨x, u, v, hx, hv, log⟩ := Finite.mem_bind.mp obs
  have pref : (l * r).toList <+: (u * v).toList := by
    rw [log]
  obtain ⟨rfl, rfl⟩ := match_prefix hm ha hx pref
  have words : l.toList ++ v.toList = l.toList ++ r.toList := congrArg FreeMonoid.toList log
  have same : v = r := FreeMonoid.ext (List.append_cancel_left words)
  exact same ▸ hv

/-- Cancel a common success prefix precisely on its reachable continuations.
The prefix may have effects and reply-dependent length. -/
theorem bind_eq_iff_for_replies_proof {A B : Type} {m : Trace α Φ A} (hm : PrefixDetermined m)
    (k l : A → Trace α Φ B) :
    (m >>= k) = (m >>= l) ↔ ∀ a w, (a, w) ∈ m.outcomes → k a = l a := by
  constructor
  · intro eq a w reachable
    apply Finite.outcomes_injective
    ext ⟨b, u⟩
    constructor
    · intro obs
      apply cancel_mem hm reachable
      rw [← eq]
      exact Finite.mem_bind.mpr ⟨a, w, u, reachable, obs, rfl⟩
    · intro obs
      apply cancel_mem hm reachable
      rw [eq]
      exact Finite.mem_bind.mpr ⟨a, w, u, reachable, obs, rfl⟩
  · intro eq
    apply Finite.outcomes_injective
    ext ⟨b, u⟩
    simp only [Finite.mem_bind]
    constructor <;> rintro ⟨a, l', r, ha, hr, log⟩
    · exact ⟨a, l', r, ha, eq a l' ha ▸ hr, log⟩
    · exact ⟨a, l', r, ha, (eq a l' ha).symm ▸ hr, log⟩

private theorem run_case {n : Nat} {β : BoundCtx (Ty α) n}
    {A B D : Ty α} {scr : Tm Empty Φ n} {l r : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dr : Derivation Φ Γ₀ (β.snoc B) r D)
    (ρ : BoundEnv Value β) :
    run (.case d dl dr) ρ =
      (run d ρ >>= Sum.elim (fun a => run dl (ρ.snoc a)) (fun b => run dr (ρ.snoc b))) := by
  unfold run
  simp only [Derivation.denote]
  congr 1
  funext x
  cases x <;> rfl

theorem run_case_eq_iff_replies_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {A B D : Ty α} {scr : Tm Empty Φ n} {l l' r r' : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dl' : Derivation Φ Γ₀ (β.snoc A) l' D)
    (dr : Derivation Φ Γ₀ (β.snoc B) r D) (dr' : Derivation Φ Γ₀ (β.snoc B) r' D)
    (ρ : BoundEnv Value β) :
    run (.case d dl dr) ρ = run (.case d dl' dr') ρ ↔ RepliesAgree d dl dl' dr dr' ρ := by
  rw [run_case, run_case, bind_eq_iff_for_replies_proof (run_prefix_determined_proof d ρ)]
  constructor
  · intro equal
    exact ⟨fun a w h => equal (.inl a) w h, fun b w h => equal (.inr b) w h⟩
  · intro arms x w h
    cases x with
    | inl a => exact arms.1 a w h
    | inr b => exact arms.2 b w h

theorem run_op_reaches_reply_proof {n : Nat} {β : BoundCtx (Ty α) n} {arg : Tm Empty Φ n}
    (f : Φ) (d : Derivation Φ Γ₀ β arg (instrSrc f)) (ρ : BoundEnv Value β)
    (reply : Value (instrTrg f)) :
    (∃ w, (reply, w) ∈ (run (.op (f := f) d) ρ).outcomes) ↔ (run d ρ).outcomes.Nonempty := by
  change (∃ w, (reply, w) ∈ (run d ρ >>= (model (α := α)).eval f).outcomes) ↔ _
  constructor
  · rintro ⟨w, h⟩
    obtain ⟨a, u, _, ha, _, _⟩ := Finite.mem_bind.mp h
    exact ⟨(a, u), ha⟩
  · rintro ⟨⟨a, u⟩, ha⟩
    let event := FreeMonoid.of (Event.mk (α := α) f a reply)
    exact ⟨u * event, Finite.mem_bind.mpr ⟨a, u, event, ha, ⟨reply, rfl⟩, rfl⟩⟩

end Silmaril.Isotope.LetCase.Structural.Reply
