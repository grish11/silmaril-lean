module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Semantics.ITree.Thms
public import Mathlib.Data.Stream.Init
public import Silmaril.Games.Abstract.Module.Defs
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Faithful

/-!
# Infinite import streams are the limits of pending prefixes

Partial paths (`Reach`) of an interaction tree are unique: the tree is
deterministic given the answers. So an infinite stream of answered calls is
a run of the tree exactly when each of its finite prefixes is reachable
(equivalently, pending): the limit is taken for free, with no König-style
compactness or receptivity hypothesis. Determinism is necessary: a union of
trees, one per length, has every prefix of a stream pending without any
member running it (`union_counterexample`).

Streams also decompose through a bind: an infinite run of `t >>= k` is an
infinite run of `t`, or a finished run of `t` to `v` followed by an infinite
run of `k v` (`infPath_bind_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {Y Z : Type (u + 1)}

/-! ## Partial paths -/

/-- `Reach t cs t'`: after the answered calls `cs`, `t` continues as `t'`. -/
inductive Reach : Tree (SigEv E) Y → List (Call E) → Tree (SigEv E) Y → Prop
  | nil {t} : Reach t [] t
  | vis {t : Tree (SigEv E) Y} {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y} {r : R}
      {cs : List (Call E)} {t' : Tree (SigEv E) Y} :
      t = vis e k → Reach (k r) cs t' → Reach t (⟨e.1, cast e.2.symm r⟩ :: cs) t'

theorem reach_nil_inv {t t' : Tree (SigEv E) Y} (h : Reach t [] t') : t' = t := by
  cases h; rfl

theorem reach_cons_inv {t t' : Tree (SigEv E) Y} {c : Call E} {cs : List (Call E)}
    (h : Reach t (c :: cs) t') :
    ∃ (R : Type u) (e : SigEv E R) (k : R → Tree (SigEv E) Y) (r : R),
      t = vis e k ∧ c = ⟨e.1, cast e.2.symm r⟩ ∧ Reach (k r) cs t' := by
  cases h with
  | vis ht hr => exact ⟨_, _, _, _, ht, rfl, hr⟩

theorem reach_unique {t t₁ t₂ : Tree (SigEv E) Y} {cs : List (Call E)}
    (h₁ : Reach t cs t₁) (h₂ : Reach t cs t₂) : t₁ = t₂ := by
  induction cs generalizing t with
  | nil => rw [reach_nil_inv h₁, reach_nil_inv h₂]
  | cons c cs ih =>
    obtain ⟨R, e, k, r, rfl, rfl, hr⟩ := reach_cons_inv h₁
    obtain ⟨R', e', k', r', ht, hc, hr'⟩ := reach_cons_inv h₂
    obtain ⟨rfl, he, hk⟩ := vis_heq ht
    obtain rfl := eq_of_heq he
    obtain rfl := eq_of_heq hk
    obtain rfl := call_answer_inj e.2 hc
    exact ih hr hr'

theorem reach_append {t t'' : Tree (SigEv E) Y} {cs₁ cs₂ : List (Call E)} :
    Reach t (cs₁ ++ cs₂) t'' ↔ ∃ t', Reach t cs₁ t' ∧ Reach t' cs₂ t'' := by
  induction cs₁ generalizing t with
  | nil => exact ⟨fun h => ⟨t, .nil, h⟩, fun ⟨t', h₁, h₂⟩ => reach_nil_inv h₁ ▸ h₂⟩
  | cons c cs ih =>
    constructor
    · intro h
      obtain ⟨R, e, k, r, rfl, rfl, hr⟩ := reach_cons_inv h
      obtain ⟨t', h₁, h₂⟩ := ih.1 hr
      exact ⟨t', .vis rfl h₁, h₂⟩
    · rintro ⟨t', h₁, h₂⟩
      obtain ⟨R, e, k, r, rfl, rfl, hr⟩ := reach_cons_inv h₁
      exact .vis rfl (ih.2 ⟨t', hr, h₂⟩)

theorem reach_single {t t'' : Tree (SigEv E) Y} {c : Call E} :
    Reach t [c] t'' ↔ ∃ (R : Type u) (e : SigEv E R) (k : R → Tree (SigEv E) Y) (r : R),
      t = vis e k ∧ c = ⟨e.1, cast e.2.symm r⟩ ∧ t'' = k r := by
  constructor
  · intro h
    obtain ⟨R, e, k, r, ht, hc, hr⟩ := reach_cons_inv h
    exact ⟨R, e, k, r, ht, hc, reach_nil_inv hr⟩
  · rintro ⟨R, e, k, r, rfl, rfl, rfl⟩
    exact .vis rfl .nil

theorem pend_iff_reach {t : Tree (SigEv E) Y} {cs : List (Call E)} {m : E.Op} :
    Pend t cs m ↔ ∃ (R : Type u) (e : SigEv E R) (k : R → Tree (SigEv E) Y),
      Reach t cs (vis e k) ∧ e.1 = m := by
  constructor
  · intro h
    induction h with
    | here ht => exact ⟨_, _, _, by rw [ht]; exact Reach.nil, rfl⟩
    | vis ht _ ih =>
      obtain ⟨R, e, k, hr, hm⟩ := ih
      exact ⟨R, e, k, .vis ht hr, hm⟩
  · rintro ⟨R, e, k, hr, rfl⟩
    induction cs generalizing t with
    | nil => rw [← reach_nil_inv hr]; exact .here rfl
    | cons c cs ih =>
      obtain ⟨R', e', k', r, rfl, rfl, hr'⟩ := reach_cons_inv hr
      exact .vis rfl (ih hr')

theorem reach_of_path {t : Tree (SigEv E) Y} {cs : List (Call E)} {v : Y}
    (h : Path t cs (.val v)) : Reach t cs (ret v) := by
  generalize hv : (PathEnd.val v : PathEnd Y) = rv at h
  induction h with
  | ret ht => cases hv; exact ht ▸ .nil
  | div _ => cases hv
  | vis ht _ ih => exact .vis ht (ih hv)

theorem reach_ret {v : Y} {cs : List (Call E)} {t' : Tree (SigEv E) Y}
    (h : Reach (ret v) cs t') : cs = [] ∧ t' = ret v := by
  cases cs with
  | nil => exact ⟨rfl, reach_nil_inv h⟩
  | cons c cs =>
    obtain ⟨R, e, k, r, ht, -, -⟩ := reach_cons_inv h
    exact absurd ht (ret_ne_vis _ _ _)

/-- Two finished returning paths whose call lists are comparable are equal. -/
theorem path_val_unique {t : Tree (SigEv E) Y} {c c' x y : List (Call E)} {v v' : Y}
    (h : Path t c (.val v)) (h' : Path t c' (.val v')) (he : c ++ x = c' ++ y) :
    c = c' ∧ v = v' := by
  have r := reach_of_path h
  have r' := reach_of_path h'
  rcases List.append_eq_append_iff.1 he with ⟨a', rfl, -⟩ | ⟨c'', rfl, -⟩
  · obtain ⟨t₁, h₁, h₂⟩ := reach_append.1 r'
    obtain rfl := reach_unique r h₁
    obtain ⟨rfl, hv⟩ := reach_ret h₂
    exact ⟨by simp, (ret_inj.1 hv).symm⟩
  · obtain ⟨t₁, h₁, h₂⟩ := reach_append.1 r
    obtain rfl := reach_unique r' h₁
    obtain ⟨rfl, hv⟩ := reach_ret h₂
    exact ⟨by simp, ret_inj.1 hv⟩

/-! ## Streams and prefixes -/

theorem infPath_iff_reach {t : Tree (SigEv E) Y} {ω : Stream' (Call E)} :
    InfPath t ω ↔ ∀ n, ∃ t', Reach t (ω.take n) t' := by
  constructor
  · rintro ⟨τ, h0, hτ⟩
    have key : ∀ n, Reach t (ω.take n) (τ n) := by
      intro n
      induction n with
      | zero => rw [h0]; exact .nil
      | succ n ih =>
        rw [Stream'.take_succ']
        obtain ⟨R, e, k, r, h₁, h₂, h₃⟩ := hτ n
        exact reach_append.2 ⟨τ n, ih, reach_single.2 ⟨R, e, k, r, h₁, h₂, h₃⟩⟩
    exact fun n => ⟨τ n, key n⟩
  · intro h
    choose τ hτ using h
    refine ⟨τ, reach_unique (hτ 0) .nil, fun n => ?_⟩
    have h1 := hτ (n + 1)
    rw [Stream'.take_succ'] at h1
    obtain ⟨t', ht', hs⟩ := reach_append.1 h1
    obtain rfl := reach_unique ht' (hτ n)
    obtain ⟨R, e, k, r, h₁, h₂, h₃⟩ := reach_single.1 hs
    exact ⟨R, e, k, r, h₁, h₂, h₃⟩

theorem infPath_iff_pend {t : Tree (SigEv E) Y} {ω : Stream' (Call E)} :
    InfPath t ω ↔ ∀ n, ∃ m, Pend t (ω.take n) m := by
  rw [infPath_iff_reach]
  constructor
  · intro h n
    obtain ⟨t', h₁⟩ := h (n + 1)
    rw [Stream'.take_succ'] at h₁
    obtain ⟨t'', h₂, hs⟩ := reach_append.1 h₁
    obtain ⟨R, e, k, r, rfl, -, -⟩ := reach_single.1 hs
    exact ⟨e.1, pend_iff_reach.2 ⟨R, e, k, h₂, rfl⟩⟩
  · intro h n
    obtain ⟨m, hm⟩ := h n
    obtain ⟨R, e, k, hr, -⟩ := pend_iff_reach.1 hm
    exact ⟨_, hr⟩

theorem streamPrefix_iff {α : Type u} {l : List α} {ω : Stream' α} :
    Shape.StreamPrefix l ω ↔ l = ω.take l.length := by
  constructor
  · intro h
    refine List.ext_getElem (by simp [Stream'.length_take]) fun i h₁ h₂ => ?_
    rw [← h i h₁]
    have := Stream'.getElem?_take (s := ω) (k := i) (n := l.length) h₁
    rw [List.getElem?_eq_getElem h₂] at this
    exact (Option.some.inj this).symm
  · intro h i hi
    have := Stream'.getElem?_take (s := ω) (k := i) (n := l.length) hi
    rw [← h, List.getElem?_eq_getElem hi] at this
    exact (Option.some.inj this).symm

theorem infPath_iff_streamPrefix {t : Tree (SigEv E) Y} {ω : Stream' (Call E)} :
    InfPath t ω ↔ ∀ l, Shape.StreamPrefix l ω → ∃ m, Pend t l m := by
  rw [infPath_iff_pend]
  constructor
  · intro h l hl
    rw [streamPrefix_iff.1 hl]
    exact h _
  · intro h n
    exact h _ (streamPrefix_iff.2 (by rw [Stream'.length_take]))

/-! ## Determinism is necessary -/

/-- One import, answered with no data. -/
def oneImport : Sig.{0} := ⟨PUnit, fun _ => PUnit⟩

/-- Call the import `n` times, then return. -/
noncomputable def callTimes : Nat → Tree (SigEv oneImport) PUnit.{2}
  | 0 => ret ⟨⟩
  | n + 1 => vis (R := PUnit) (⟨⟨⟩, rfl⟩ : SigEv oneImport PUnit) fun _ => callTimes n

/-- The stream calling the import forever. -/
def forever : Stream' (Call oneImport) := fun _ => ⟨⟨⟩, ⟨⟩⟩

theorem pend_callTimes (n : Nat) : Pend (callTimes (n + 1)) (forever.take n) ⟨⟩ := by
  induction n with
  | zero => exact .here rfl
  | succ n ih => exact .vis (n := ⟨⟩) rfl ih

theorem pend_callTimes_length {i : Nat} {cs : List (Call oneImport)} {m : oneImport.Op}
    (h : Pend (callTimes i) cs m) : cs.length < i := by
  induction i generalizing cs with
  | zero => exact absurd h not_pend_ret
  | succ i ih =>
    rcases pend_vis_inv h with ⟨rfl, -⟩ | ⟨n, cs', rfl, hp⟩
    · simp
    · simpa using ih hp

/-- The pending prefixes of the union of the `callTimes i` have the limit
`forever`, but no `callTimes i` runs forever. -/
theorem union_counterexample :
    (∀ n, ∃ i m, Pend (callTimes i) (forever.take n) m) ∧ ∀ i ω, ¬ InfPath (callTimes i) ω := by
  refine ⟨fun n => ⟨n + 1, ⟨⟩, pend_callTimes n⟩, fun i ω h => ?_⟩
  obtain ⟨m, hm⟩ := infPath_iff_pend.1 h i
  have := pend_callTimes_length hm
  rw [show (Stream'.take i ω).length = i from Stream'.length_take i ω] at this
  exact lt_irrefl _ this

/-! ## Through a bind -/

theorem reach_bind {t t' : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y} {cs : List (Call E)}
    (h : Reach t cs t') : Reach (t >>= k) cs (t' >>= k) := by
  induction h with
  | nil => exact .nil
  | vis ht _ ih => rw [ht, vis_bind]; exact .vis rfl ih

theorem reach_bind_inv {t : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y} {cs : List (Call E)}
    {T : Tree (SigEv E) Y} (h : Reach (t >>= k) cs T) :
    (∃ t', Reach t cs t' ∧ T = t' >>= k) ∨
      ∃ cs₁ v cs₂, Path t cs₁ (.val v) ∧ Reach (k v) cs₂ T ∧ cs = cs₁ ++ cs₂ := by
  induction cs generalizing t with
  | nil => exact .inl ⟨t, .nil, reach_nil_inv h⟩
  | cons c cs ih =>
    obtain ⟨R, e, K, r, hv, rfl, hr⟩ := reach_cons_inv h
    rcases cases_visible t with rfl | ⟨v, rfl⟩ | ⟨R', e', k', rfl⟩
    · rw [diverge_bind] at hv; exact absurd hv.symm (vis_ne_diverge _ _)
    · rw [show (ret v >>= k) = k v from pure_bind v k] at hv
      exact .inr ⟨[], v, _, .ret rfl, hv ▸ .vis rfl hr, rfl⟩
    · rw [vis_bind] at hv
      obtain ⟨rfl, he, hk⟩ := vis_heq hv
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      rcases ih hr with ⟨t', h₁, rfl⟩ | ⟨cs₁, v, cs₂, h₁, h₂, rfl⟩
      · exact .inl ⟨t', .vis rfl h₁, rfl⟩
      · exact .inr ⟨_ :: cs₁, v, cs₂, .vis rfl h₁, h₂, rfl⟩

theorem infPath_bind_iff {t : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y}
    {ω : Stream' (Call E)} :
    InfPath (t >>= k) ω ↔ InfPath t ω ∨
      ∃ (cs : List (Call E)) (v : Z) (ω' : Stream' (Call E)), Path t cs (.val v) ∧ InfPath (k v) ω' ∧ ω = cs ++ₛ ω' := by
  constructor
  · intro h
    rw [infPath_iff_reach] at h
    by_cases ht : ∀ n, ∃ t', Reach t (ω.take n) t'
    · exact .inl (infPath_iff_reach.2 ht)
    · push Not at ht
      obtain ⟨N, hN⟩ := ht
      obtain ⟨T, hT⟩ := h N
      rcases reach_bind_inv hT with ⟨t', h₁, -⟩ | ⟨cs₁, v, cs₂, h₁, -, hc⟩
      · exact absurd h₁ (hN t')
      · have hpre : ω.take cs₁.length = cs₁ := by
          have := congrArg (List.take cs₁.length) hc
          rw [Stream'.take_take, List.take_left] at this
          rwa [show min N cs₁.length = cs₁.length from by
            have := congrArg List.length hc
            rw [Stream'.length_take, List.length_append] at this
            omega] at this
        have hω : ω = cs₁ ++ₛ ω.drop cs₁.length := by
          conv_lhs => rw [← Stream'.append_take_drop cs₁.length ω]
          rw [hpre]
        refine .inr ⟨cs₁, v, ω.drop cs₁.length, h₁, infPath_iff_reach.2 fun j => ?_, hω⟩
        obtain ⟨T', hT'⟩ := h (cs₁.length + j)
        rw [hω, ← Stream'.append_take] at hT'
        rcases reach_bind_inv hT' with ⟨t', h₂, -⟩ | ⟨cs₁', v', cs₂', h₂, h₃, hc'⟩
        · obtain ⟨t₁, h₄, h₅⟩ := reach_append.1 h₂
          obtain rfl := reach_unique (reach_of_path h₁) h₄
          obtain ⟨hj, -⟩ := reach_ret h₅
          exact ⟨k v, by rw [hj]; exact .nil⟩
        · obtain ⟨rfl, rfl⟩ := path_val_unique h₁ h₂ hc'
          rw [List.append_cancel_left hc']
          exact ⟨T', h₃⟩
  · rintro (⟨τ, h0, hτ⟩ | ⟨cs, v, ω', hp, hi, rfl⟩)
    · refine ⟨fun n => τ n >>= k, by show τ 0 >>= k = _; rw [h0], fun n => ?_⟩
      obtain ⟨R, e, k', r, h₁, h₂, h₃⟩ := hτ n
      exact ⟨R, e, fun r => k' r >>= k, r, by show τ n >>= k = _; rw [h₁, vis_bind], h₂,
        by show τ (n + 1) >>= k = _; rw [h₃]⟩
    · have hi := infPath_iff_reach.1 hi
      refine infPath_iff_reach.2 ?_
      have hr := reach_of_path hp
      intro n
      by_cases hn : n ≤ cs.length
      · rw [Stream'.take_append_of_le_length _ _ _ hn]
        have hsplit := List.take_append_drop n cs
        rw [← hsplit] at hr
        obtain ⟨t', h₁, -⟩ := reach_append.1 hr
        exact ⟨_, reach_bind h₁⟩
      · obtain ⟨j, rfl⟩ : ∃ j, n = cs.length + j := ⟨n - cs.length, by omega⟩
        rw [← Stream'.append_take]
        obtain ⟨T, hT⟩ := hi j
        have h₁ := reach_bind (k := k) hr
        rw [show (ret v >>= k) = k v from pure_bind v k] at h₁
        exact ⟨T, reach_append.2 ⟨k v, h₁, hT⟩⟩

theorem not_infPath_ret {v : Y} {ω : Stream' (Call E)} : ¬ InfPath (ret v) ω := by
  rintro ⟨τ, h0, hτ⟩
  obtain ⟨R, e, k, r, h₁, -, -⟩ := hτ 0
  rw [h0] at h₁
  exact ret_ne_vis _ _ _ h₁

theorem not_infPath_diverge {ω : Stream' (Call E)} : ¬ InfPath (diverge : Tree (SigEv E) Y) ω := by
  rintro ⟨τ, h0, hτ⟩
  obtain ⟨R, e, k, r, h₁, -, -⟩ := hτ 0
  rw [h0] at h₁
  exact vis_ne_diverge _ _ h₁.symm

/-! ## Bodies -/

/-- The inverse of `liftCall`. -/
def lowerCall (c : Call (liftSig E)) : Call E := ⟨c.1.down, c.2.down⟩

theorem liftCall_lowerCall (c : Call (liftSig E)) : liftCall (lowerCall c) = c := rfl

theorem lowerCall_liftCall (c : Call E) : lowerCall (liftCall c) = c := rfl

theorem take_map.{v, w} {α : Type v} {β : Type w} (f : α → β) (ω : Stream' α) (n : Nat) :
    (Stream'.map f ω).take n = (ω.take n).map f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Stream'.take_succ', Stream'.take_succ', ih, List.map_append]; rfl

variable {S T A B C : Type (u + 1)}

theorem mem_toInf_iff (f : Hom E S T A B) (s : S) (a : A) (ω : Nat → Call (liftSig E)) :
    ω ∈ toInf f s a ↔ ∀ n, ∃ m, (Stream'.take n ω, m) ∈ toPending f s a := by
  constructor
  · rintro ⟨ω', hω', rfl⟩ n
    obtain ⟨m, hm⟩ := infPath_iff_pend.1 hω' n
    exact ⟨_, ⟨_, m, hm, Prod.ext (take_map liftCall ω' n) rfl⟩⟩
  · intro h
    refine ⟨Stream'.map lowerCall ω, infPath_iff_pend.2 fun n => ?_, rfl⟩
    obtain ⟨_, cs, m, hm, he⟩ := h n
    have he1 : Stream'.take n ω = cs.map liftCall := congrArg Prod.fst he
    have : cs = Stream'.take n (Stream'.map lowerCall ω) := by
      have h2 : Stream'.take n (Stream'.map lowerCall ω) = cs := by
        refine (take_map lowerCall ω n).trans ?_
        rw [he1, List.map_map]
        exact (List.map_congr_left fun c _ => rfl).trans (List.map_id cs)
      exact h2.symm
    exact ⟨m, this ▸ hm⟩

theorem mem_toInf_iff_streamPrefix (f : Hom E S T A B) (s : S) (a : A)
    (ω : Nat → Call (liftSig E)) :
    ω ∈ toInf f s a ↔ ∀ l, Shape.StreamPrefix l ω → ∃ m, (l, m) ∈ toPending f s a := by
  rw [mem_toInf_iff]
  constructor
  · intro h l hl
    rw [streamPrefix_iff.1 hl]
    exact h _
  · intro h n
    exact h _ (streamPrefix_iff.2 (by
      rw [show (Stream'.take n ω).length = n from Stream'.length_take n ω]))

theorem toInf_eq_of_toPending {f g : Hom E S T A B} (h : toPending f = toPending g) :
    toInf f = toInf g := by
  funext s a; ext ω; exact (mem_toInf_iff f s a ω).trans (h ▸ (mem_toInf_iff g s a ω).symm)

theorem toInf_comp (f : Hom E S T A B) (g : Hom E S T B C) (s : S) (a : A) :
    toInf (fun a => f a >>= g) s a = toInf f s a ∪
      {ω | ∃ (c : List (Call (liftSig E))) (b : B) (s₁ : S) (ω' : Stream' (Call (liftSig E))),
        (c, End.ret b s₁) ∈ toAFun f s a ∧
        ω' ∈ toInf g s₁ b ∧ ω = c ++ₛ ω'} := by
  ext ω
  constructor
  · rintro ⟨ω', hω', rfl⟩
    rw [run_bind] at hω'
    rcases infPath_bind_iff.1 hω' with h | ⟨cs, v, ω'', hp, hi, rfl⟩
    · exact .inl ⟨ω', h, rfl⟩
    · rcases v with e | ⟨b, s₁⟩
      · exact absurd hi not_infPath_ret
      · refine .inr ⟨cs.map liftCall, b, s₁, liftCall ∘ ω'', ⟨cs, _, hp, rfl⟩, ⟨ω'', hi, rfl⟩, ?_⟩
        exact (Stream'.map_append_stream liftCall cs ω'')
  · rintro (⟨ω', h, rfl⟩ | ⟨c, b, s₁, ω', ⟨cs, r, hp, he⟩, ⟨ω'', hi, rfl⟩, rfl⟩)
    · refine ⟨ω', ?_, rfl⟩
      rw [run_bind]
      exact infPath_bind_iff.2 (.inl h)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain rfl := endOf_eq_ret he.symm
      refine ⟨cs ++ₛ ω'', ?_, (Stream'.map_append_stream liftCall cs ω'').symm⟩
      rw [run_bind]
      exact infPath_bind_iff.2 (.inr ⟨cs, _, ω'', hp, hi, rfl⟩)

end Silmaril.Proofs.Wasm.Abstract.BodyTrace
