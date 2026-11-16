module

public import Silmaril.Proofs.Games.Abstract.SessionHost.Host
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
public import Silmaril.Games.DivComp.Defs
import Mathlib.Data.List.Induction

/-!
# The finite plays of a session with host imports (proofs)

The session of `t` composed with the host beside copycat has the finite plays of the session of
`hostLinkS R t`.

* `fwd`: a run of the automaton of `t` with allowed host answers gives a run of the linked
  automaton on its visible part, the states related by `J`;
* `bwd`: conversely, a run of the linked automaton is the visible part of a run of `t`. The run of
  `t` is built from the end: the call prefix witnessing the last visible call fixes the hidden host
  calls before it (`StratObs.satP_prefix`), so every state of the linked run is related (`K`) to a
  state of `t` reached by its call prefixes (`Reach`);
* `satP_hostLinkS`: the linked triple is saturated, so every linked call has a witness.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost
  Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession

universe u

variable {E F : Sig.{u}} {S A B : Type u} {R : HostRel E}

/-! ## Lists and streams -/

section Lists

variable {G : Sig.{u}}

@[simp] theorem callMoves_nil' : (callMoves ([] : List (Call E)) : List (Move E G)) = [] := rfl

@[simp] theorem callMoves_cons' (x : Call E) (c : List (Call E)) :
    (callMoves (x :: c) : List (Move E G)) =
      .inl (.ask x.1) :: .inl (.ans x.1 x.2) :: callMoves c := rfl

@[simp] theorem callMoves_append' (c d : List (Call E)) :
    (callMoves (c ++ d) : List (Move E G)) = callMoves c ++ callMoves d := by
  simp [callMoves]

theorem length_callMoves' (c : List (Call E)) :
    (callMoves c : List (Move E G)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

theorem streamTake_succ' {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

@[simp] theorem length_streamTake' {α : Type u} (ω : ℕ → α) (k : ℕ) :
    (streamTake ω k).length = k := by
  simp [streamTake]

theorem streamTake_mono {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j ≤ k) :
    streamTake ω j <+: streamTake ω k := by
  induction k with
  | zero => cases Nat.le_zero.1 h; exact List.prefix_refl _
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact (ih (Nat.lt_succ_iff.1 h)).trans
        (by rw [streamTake_succ']; exact List.prefix_append _ _)
    · exact List.prefix_refl _

theorem eq_of_snoc_eq {α : Type u} {l l' : List α} {x x' : α} (h : l ++ [x] = l' ++ [x']) :
    l = l' ∧ x = x' := by
  have h1 := congrArg List.dropLast h
  have h2 := congrArg List.getLast? h
  simp at h1 h2
  exact ⟨h1, h2⟩

/-- A call prefix of a stream prefix is a stream prefix. -/
theorem callPre_streamTake {ω : ℕ → Call E} {n : ℕ} {c : List (Call E)} {m : E.Op}
    (h : CallPre c m (streamTake ω n)) : ∃ k, streamTake ω k = c ∧ (ω k).1 = m := by
  obtain ⟨x, d, hd⟩ := h
  have hlen : c.length + 1 ≤ n := by
    have := congrArg List.length hd; simp at this; omega
  have h₁ : streamTake ω (c.length + 1) <+: streamTake ω n := streamTake_mono ω hlen
  have h₂ : c ++ [⟨m, x⟩] <+: streamTake ω n := ⟨d, by simp [hd]⟩
  have heq : streamTake ω (c.length + 1) = c ++ [⟨m, x⟩] :=
    List.IsPrefix.eq_of_length (List.prefix_of_prefix_length_le h₁ h₂ (by simp))
      (by simp)
  rw [streamTake_succ'] at heq
  obtain ⟨h₄, h₅⟩ := eq_of_snoc_eq heq
  exact ⟨c.length, h₄, by rw [h₅]⟩

/-- A call prefix after one more call. -/
theorem callPre_snoc {c c₀ : List (Call E)} {x : Call E} {m : E.Op}
    (h : CallPre c₀ m (c ++ [x])) : (c₀ = c ∧ m = x.1) ∨ CallPre c₀ m c := by
  obtain ⟨n, d, hd⟩ := h
  rcases List.eq_nil_or_concat d with rfl | ⟨d', z, rfl⟩
  · obtain ⟨h₁, h₂⟩ := eq_of_snoc_eq hd
    exact .inl ⟨h₁.symm, by rw [h₂]⟩
  · rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at hd
    exact .inr ⟨n, d', (eq_of_snoc_eq hd).1⟩

theorem callPre_prefix {c₀ c : List (Call E)} {m : E.Op} (h : CallPre c₀ m c) : c₀ <+: c := by
  obtain ⟨n, d, rfl⟩ := h; exact List.prefix_append _ _

end Lists

/-! ## Component calls and allowed logs -/

section Calls

@[simp] theorem fCalls_nil : fCalls ([] : List (Call (E ⊕ₛ F))) = [] := rfl

@[simp] theorem fCalls_cons (x : Call (E ⊕ₛ F)) (c : List (Call (E ⊕ₛ F))) :
    fCalls (x :: c) = fCall x ++ fCalls c := rfl

@[simp] theorem fCalls_append (c d : List (Call (E ⊕ₛ F))) :
    fCalls (c ++ d) = fCalls c ++ fCalls d := by
  induction c with
  | nil => rfl
  | cons x c ih => rw [List.cons_append, fCalls_cons, fCalls_cons, ih, List.append_assoc]

@[simp] theorem fCall_inl (m : E.Op) (n : (E ⊕ₛ F).Ar (.inl m)) :
    fCall (⟨.inl m, n⟩ : Call (E ⊕ₛ F)) = [] := rfl

@[simp] theorem fCall_inr (m : F.Op) (n : (E ⊕ₛ F).Ar (.inr m)) :
    fCall (⟨.inr m, n⟩ : Call (E ⊕ₛ F)) = [(⟨m, n⟩ : Call F)] := rfl

theorem fCalls_prefix {c d : List (Call (E ⊕ₛ F))} (h : c <+: d) : fCalls c <+: fCalls d := by
  obtain ⟨u, rfl⟩ := h; rw [fCalls_append]; exact List.prefix_append _ _

/-- The allowed logs. -/
abbrev Ok (R : HostRel E) (F : Sig.{u}) (c : List (Call (E ⊕ₛ F))) : Prop := (sumL R F).Consistent c

theorem Ok.nil : Ok R F [] := fun _ h => nomatch h

theorem ok_append {c d : List (Call (E ⊕ₛ F))} : Ok R F (c ++ d) ↔ Ok R F c ∧ Ok R F d := by
  simp only [Ok, HostRel.Consistent, List.mem_append, or_imp, forall_and]

theorem Ok.of_prefix {c d : List (Call (E ⊕ₛ F))} (h : Ok R F d) (hc : c <+: d) : Ok R F c :=
  fun x hx => h x (hc.subset hx)

theorem ok_inr {c : List (Call (E ⊕ₛ F))} {m : F.Op} {n : F.Ar m} (h : Ok R F c) :
    Ok R F (c ++ [⟨.inr m, n⟩]) :=
  ok_append.2 ⟨h, fun x hx => by cases List.mem_singleton.1 hx; trivial⟩

theorem ok_inl {c : List (Call (E ⊕ₛ F))} {m : E.Op} {n : E.Ar m} (h : Ok R F c)
    (hn : R m (.answer n)) : Ok R F (c ++ [⟨.inl m, n⟩]) :=
  ok_append.2 ⟨h, fun x hx => by cases List.mem_singleton.1 hx; exact hn⟩

/-- A call prefix of the component calls lifts to a call prefix. -/
theorem callPre_fCalls {c' : List (Call F)} {m : F.Op} :
    ∀ {c : List (Call (E ⊕ₛ F))}, CallPre c' m (fCalls c) →
      ∃ c₀, CallPre c₀ (.inr m : (E ⊕ₛ F).Op) c ∧ fCalls c₀ = c' := by
  intro c
  induction c generalizing c' with
  | nil => rintro ⟨n, d, h⟩; simp at h
  | cons x c ih =>
    rintro ⟨n, d, h⟩
    rcases x with ⟨μ | μ, ν⟩
    · rw [fCalls_cons, fCall_inl, List.nil_append] at h
      obtain ⟨c₀, ⟨n₀, d₀, hd₀⟩, hc₀⟩ := ih ⟨n, d, h⟩
      exact ⟨⟨.inl μ, ν⟩ :: c₀, ⟨n₀, d₀, by rw [hd₀]; rfl⟩, by rw [fCalls_cons, hc₀]; rfl⟩
    · rw [fCalls_cons, fCall_inr, List.singleton_append] at h
      rcases c' with _ | ⟨y, c'⟩
      · rw [List.nil_append, List.cons.injEq] at h
        obtain ⟨h₁, -⟩ := h
        cases h₁
        exact ⟨[], ⟨_, c, rfl⟩, rfl⟩
      · rw [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨c₀, ⟨n₀, d₀, hd₀⟩, hc₀⟩ := ih ⟨n, d, h⟩
        exact ⟨⟨.inr μ, ν⟩ :: c₀, ⟨n₀, d₀, by rw [hd₀]; rfl⟩, by rw [fCalls_cons, hc₀]; rfl⟩

/-- `fCalls c₁` ends with a component call: split `c₁` at it. -/
theorem split_fCalls {c' : List (Call F)} {m : F.Op} {n : F.Ar m} :
    ∀ {c₁ : List (Call (E ⊕ₛ F))}, fCalls c₁ = c' ++ [⟨m, n⟩] →
      ∃ c seg, c₁ = c ++ ⟨.inr m, n⟩ :: seg ∧ fCalls c = c' ∧ fCalls seg = [] := by
  intro c₁
  induction c₁ using List.reverseRecOn with
  | nil => intro h; simp at h
  | append_singleton d x ih =>
    intro h
    rcases x with ⟨μ | μ, ν⟩
    · rw [fCalls_append] at h
      change fCalls d ++ [] = _ at h
      rw [List.append_nil] at h
      obtain ⟨c, seg, rfl, h₁, h₂⟩ := ih h
      exact ⟨c, seg ++ [⟨.inl μ, ν⟩], by rw [List.append_assoc, List.cons_append], h₁,
        by rw [fCalls_append, h₂]; rfl⟩
    · rw [fCalls_append] at h
      change fCalls d ++ [(⟨μ, ν⟩ : Call F)] = _ at h
      obtain ⟨h₁, h₂⟩ := eq_of_snoc_eq h
      cases h₂
      exact ⟨d, [], rfl, h₁, rfl⟩

end Calls

/-! ## Call prefixes reached -/

section Reach

variable {t : ObsTriple (E ⊕ₛ F) S A B} {s : S} {a : A}

/-- Every call prefix of `c` is a call prefix of `t`: the automaton of `t` reaches `c`. -/
def Reach (t : ObsTriple (E ⊕ₛ F) S A B) (s : S) (a : A) (c : List (Call (E ⊕ₛ F))) : Prop :=
  ∀ c₀ μ, CallPre c₀ μ c → (c₀, μ) ∈ satP t s a

theorem reach_nil : Reach t s a [] := by
  rintro c₀ μ ⟨n, d, h⟩; simp at h

theorem reach_of_satP {c : List (Call (E ⊕ₛ F))} {μ : (E ⊕ₛ F).Op} (h : (c, μ) ∈ satP t s a) :
    Reach t s a c := fun _ _ hc => satP_prefix h hc

theorem reach_of_beh {c : List (Call (E ⊕ₛ F))} {e : End S B} (h : (c, e) ∈ t.1 s a) :
    Reach t s a c := fun _ _ hc => .inr (.inr (.inl ⟨c, e, h, hc⟩))

theorem reach_of_stream {ω : ℕ → Call (E ⊕ₛ F)} (hω : ω ∈ t.2.2 s a) (n : ℕ) :
    Reach t s a (streamTake ω n) := fun _ _ hc => by
  obtain ⟨k, hk, hm⟩ := callPre_streamTake hc
  exact .inr (.inr (.inr ⟨ω, hω, k, hk, hm⟩))

theorem reach_snoc {c : List (Call (E ⊕ₛ F))} {μ : (E ⊕ₛ F).Op} {n : (E ⊕ₛ F).Ar μ}
    (h : (c, μ) ∈ satP t s a) : Reach t s a (c ++ [⟨μ, n⟩]) := fun _ _ hc => by
  rcases callPre_snoc hc with ⟨rfl, rfl⟩ | hc
  · exact h
  · exact satP_prefix h hc

theorem Reach.of_prefix {c d : List (Call (E ⊕ₛ F))} (h : Reach t s a d) (hc : c <+: d) :
    Reach t s a c := fun c₀ μ ⟨n, e, he⟩ => by
  obtain ⟨u, rfl⟩ := hc
  exact h c₀ μ ⟨n, e ++ u, by rw [he, List.append_assoc, List.cons_append]⟩

theorem run_callMoves {X : Sig.{u}} {f : AFun X S A B} {P : Pending X S A} (d : List (Call X))
    {c₀ : List (Call X)} (hd : ∀ c m, CallPre c m (c₀ ++ d) → (c, m) ∈ P s a) :
    TRun f P (.run s a c₀) (callMoves d) (.run s a (c₀ ++ d)) := by
  induction d generalizing c₀ with
  | nil => simpa using TRun.nil _
  | cons x d ih =>
    have h := ih (c₀ := c₀ ++ [x]) (by simpa using hd)
    simp only [List.append_assoc, List.singleton_append] at h
    exact .cons (.call s a c₀ x.1 (hd c₀ x.1 ⟨x.2, d, rfl⟩)) (.cons (.reply s a c₀ x.1 x.2) h)

/-- The linked call prefixes of a reached allowed log. -/
theorem lift_callPre {c : List (Call (E ⊕ₛ F))} (hr : Reach t s a c) (hc : Ok R F c)
    {c' : List (Call F)} {m : F.Op} (h : CallPre c' m (fCalls c)) :
    ∃ c₀, (c₀, .inr m) ∈ satP t s a ∧ Ok R F c₀ ∧ c' = fCalls c₀ := by
  obtain ⟨c₀, hp, rfl⟩ := callPre_fCalls h
  exact ⟨c₀, hr _ _ hp, hc.of_prefix (callPre_prefix hp), rfl⟩

/-- **The linked triple is saturated**: every linked call prefix is a linked pending call. -/
theorem satP_hostLinkS {c' : List (Call F)} {m : F.Op}
    (h : (c', m) ∈ satP (hostLinkS R t) s a) :
    ∃ c, (c, .inr m) ∈ satP t s a ∧ Ok R F c ∧ c' = fCalls c := by
  rcases h with h | ⟨d, m', ⟨c, hc, hok, rfl⟩, hpre⟩ | ⟨d, e, hd, hpre⟩ | ⟨ω', hω', k, hk, hm⟩
  · exact h
  · exact lift_callPre (reach_of_satP hc) hok hpre
  · rcases hd with ⟨c, hc, hok, rfl⟩ | ⟨-, ⟨c, m₀, hc, hok, -, rfl⟩ | ⟨ω, hω, n, -, rfl⟩⟩
    · exact lift_callPre (reach_of_beh hc) hok hpre
    · exact lift_callPre (reach_of_satP hc) hok hpre
    · exact lift_callPre (reach_of_stream hω.1 n) (hostObsInf_consistent hω n) hpre
  · obtain ⟨ω, hω, hun, heq⟩ := hω'
    obtain ⟨j, hj⟩ := hun (k + 1)
    have hpre : streamTake ω' (k + 1) <+: fCalls (streamTake ω j) :=
      heq j ▸ streamTake_mono ω' hj
    rw [streamTake_succ', hk] at hpre
    obtain ⟨u, hu⟩ := hpre
    subst hm
    exact lift_callPre (reach_of_stream hω.1 j) (hostObsInf_consistent hω j)
      ⟨(ω' k).2, u, by rw [← hu, List.append_assoc]; rfl⟩

end Reach

/-! ## Visible parts of calls -/

section Vis

variable {G : Sig.{u}}

theorem vis_callMoves (c : List (Call (E ⊕ₛ F))) :
    vis (callMoves c : List (Move (E ⊕ₛ F) G)) = callMoves (fCalls c) := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    rcases x with ⟨μ | μ, ν⟩
    · exact ih
    · exact congrArg (List.cons _) (congrArg (List.cons _) ih)

theorem okV_callMoves {c : List (Call (E ⊕ₛ F))} (h : Ok R F c) :
    OkV R (callMoves c : List (Move (E ⊕ₛ F) G)) := by
  induction c with
  | nil => exact OkV.nil
  | cons x c ih =>
    have hx : sumL R F x.1 (.answer x.2) := h x (.head _)
    have ih := ih fun y hy => h y (.tail _ hy)
    rcases x with ⟨μ | μ, ν⟩
    · exact okV_cons.2 ⟨trivial, okV_cons.2 ⟨hx, ih⟩⟩
    · exact okV_cons.2 ⟨trivial, okV_cons.2 ⟨trivial, ih⟩⟩

theorem ok_of_okV_callMoves {c : List (Call (E ⊕ₛ F))}
    (h : OkV R (callMoves c : List (Move (E ⊕ₛ F) G))) : Ok R F c := by
  intro x hx
  induction c with
  | nil => cases hx
  | cons y c ih =>
    simp only [callMoves_cons', okV_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · rcases x with ⟨μ | μ, ν⟩
      · exact h.2.1
      · trivial
    · exact ih h.2.2 hx

theorem visMove_relMove (o : Move (E ⊕ₛ F) (sig1 A (B ⊕ PUnit.{u + 1}))) :
    visMove (relMove o) = (visMove o).map relMove := by
  rcases o with ((m | m) | ⟨(m | m), n⟩) | (q | ⟨q, r⟩) <;> rfl

theorem vis_map_relMove (p : List (Move (E ⊕ₛ F) (sig1 A (B ⊕ PUnit.{u + 1})))) :
    vis (p.map relMove) = (vis p).map relMove := by
  induction p with
  | nil => rfl
  | cons o p ih => simp [visMove_relMove, ih]

theorem okV_map_relMove {p : List (Move (E ⊕ₛ F) (sig1 A (B ⊕ PUnit.{u + 1})))} :
    OkV R (p.map relMove) ↔ OkV R p := by
  induction p with
  | nil => exact ⟨fun _ => OkV.nil, fun _ => OkV.nil⟩
  | cons o p ih =>
    simp only [List.map_cons, okV_cons, ih]
    rcases o with ((m | m) | ⟨(m | m), n⟩) | (q | ⟨q, r⟩) <;> rfl

end Vis

/-! ## The forward simulation -/

variable {t : ObsTriple (E ⊕ₛ F) S A B}

/-- Related states of the automaton of `t` and of the linked automaton. -/
inductive J (R : HostRel E) (t : ObsTriple (E ⊕ₛ F) S A B) : TSt (E ⊕ₛ F) S A → TSt F S A → Prop
  | idle (s : S) : J R t (.idle s) (.idle s)
  | run (s : S) (a : A) (c : List (Call (E ⊕ₛ F))) : Ok R F c →
      J R t (.run s a c) (.run s a (fCalls c))
  | waitE (s : S) (a : A) (c : List (Call (E ⊕ₛ F))) (m : E.Op) : Ok R F c →
      (c, .inl m) ∈ satP t s a → J R t (.wait s a c (.inl m)) (.run s a (fCalls c))
  | waitF (s : S) (a : A) (c : List (Call (E ⊕ₛ F))) (m : F.Op) : Ok R F c →
      J R t (.wait s a c (.inr m)) (.wait s a (fCalls c) m)
  | dead : J R t .dead .dead
  | stuck (a : A) : J R t (.stuck a) (.stuck a)

theorem fwd_step {x x' : TSt (E ⊕ₛ F) S A} {o : Move (E ⊕ₛ F) (sig1 A B)}
    (h : TStep t.1 (satP t) x o x') (ho : OkMove R o) {y : TSt F S A} (hJ : J R t x y) :
    ∃ y', TRun (hostLinkS R t).1 (satP (hostLinkS R t)) y (visMove o) y' ∧ J R t x' y' := by
  cases h with
  | ask s a =>
    cases hJ
    exact ⟨_, .cons (.ask s a) (.nil _), J.run s a [] Ok.nil⟩
  | call s a c μ hP =>
    cases hJ with
    | run _ _ _ hc =>
      rcases μ with m | m
      · exact ⟨_, .nil _, J.waitE s a c m hc hP⟩
      · exact ⟨_, .cons (.call s a _ m (.inl ⟨c, hP, hc, rfl⟩)) (.nil _), J.waitF s a c m hc⟩
  | reply s a c μ n =>
    rcases μ with m | m
    · cases hJ with
      | waitE _ _ _ _ hc _ =>
        refine ⟨_, .nil _, ?_⟩
        have := J.run (R := R) (t := t) s a _ (ok_inl hc ho)
        have he : fCalls (c ++ [⟨.inl m, n⟩]) = fCalls c := by
          rw [fCalls_append]; exact List.append_nil _
        rwa [he] at this
    · cases hJ with
      | waitF _ _ _ _ hc =>
        refine ⟨_, .cons (.reply s a _ m n) (.nil _), ?_⟩
        have := J.run (R := R) (t := t) s a _ (ok_inr (F := F) (m := m) (n := n) hc)
        rw [fCalls_append] at this
        exact this
  | ret s a c b s' hb =>
    cases hJ with
    | run _ _ _ hc => exact ⟨_, .cons (.ret s a _ b s' (.inl ⟨c, hb, hc, rfl⟩)) (.nil _), J.idle s'⟩
  | trap s a c hb =>
    cases hJ with
    | run _ _ _ hc => exact ⟨_, .cons (.trap s a _ (.inl ⟨c, hb, hc, rfl⟩)) (.nil _), J.dead⟩
  | deadAsk a =>
    cases hJ
    exact ⟨_, .cons (.deadAsk a) (.nil _), J.stuck a⟩

/-- **Forward**: a run of `t` with allowed host answers is seen by the linked automaton on its
visible part. -/
theorem fwd {x x' : TSt (E ⊕ₛ F) S A} {p : List (Move (E ⊕ₛ F) (sig1 A B))}
    (h : TRun t.1 (satP t) x p x') (hp : OkV R p) {y : TSt F S A} (hJ : J R t x y) :
    ∃ y', TRun (hostLinkS R t).1 (satP (hostLinkS R t)) y (vis p) y' ∧ J R t x' y' := by
  induction h generalizing y with
  | nil => exact ⟨y, .nil _, hJ⟩
  | cons hs _ ih =>
    obtain ⟨ho, hp⟩ := okV_cons.1 hp
    obtain ⟨y₁, hy₁, hJ₁⟩ := fwd_step hs ho hJ
    obtain ⟨y', hy', hJ'⟩ := ih hp hJ₁
    exact ⟨y', hy₁.append hy', hJ'⟩

/-! ## The backward simulation -/

/-- Related states of the linked automaton and of the automaton of `t`. -/
inductive K (R : HostRel E) (t : ObsTriple (E ⊕ₛ F) S A B) : TSt F S A → TSt (E ⊕ₛ F) S A → Prop
  | idle (s : S) : K R t (.idle s) (.idle s)
  | run (s : S) (a : A) (c' : List (Call F)) (c : List (Call (E ⊕ₛ F))) : Ok R F c →
      Reach t s a c → fCalls c = c' → K R t (.run s a c') (.run s a c)
  | wait (s : S) (a : A) (c' : List (Call F)) (c : List (Call (E ⊕ₛ F))) (m : F.Op) : Ok R F c →
      (c, .inr m) ∈ satP t s a → fCalls c = c' → K R t (.wait s a c' m) (.wait s a c (.inr m))
  | dead : K R t .dead .dead
  | stuck (a : A) : K R t (.stuck a) (.stuck a)

theorem bwd_step {y y₁ : TSt F S A} {o : Move F (sig1 A B)}
    (h : TStep (hostLinkS R t).1 (satP (hostLinkS R t)) y o y₁) {x₁ : TSt (E ⊕ₛ F) S A}
    (hK : K R t y₁ x₁) : ∃ x p, K R t y x ∧ TRun t.1 (satP t) x p x₁ ∧ vis p = [o] ∧ OkV R p := by
  cases h with
  | ask s a =>
    cases hK with
    | run _ _ _ c hc hr he =>
      have h := run_callMoves (f := t.1) (P := satP t) (s := s) (a := a) c (c₀ := [])
        (by rw [List.nil_append]; exact hr)
      rw [List.nil_append] at h
      refine ⟨_, .inr (.ask a) :: callMoves c, K.idle s, .cons (.ask s a) h,
        ?_, okV_cons.2 ⟨trivial, okV_callMoves hc⟩⟩
      simp [visMove, vis_callMoves, he]
  | call s a c' m _ =>
    cases hK with
    | wait _ _ _ c _ hc hP he =>
      exact ⟨_, [.inl (.ask (.inr m))], K.run s a c' c hc (reach_of_satP hP) he,
        .cons (.call s a c (.inr m) hP) (.nil _), rfl, okV_cons.2 ⟨trivial, OkV.nil⟩⟩
  | reply s a c' m n =>
    cases hK with
    | run _ _ _ c₁ hc hr he =>
      obtain ⟨c, seg, rfl, h₁, h₂⟩ := split_fCalls he
      have hP : (c, .inr m) ∈ satP t s a := hr c (.inr m) ⟨n, seg, rfl⟩
      have hseg := run_callMoves (f := t.1) (s := s) (a := a) seg
        (c₀ := c ++ [⟨.inr m, n⟩])
        (fun c₂ μ h => hr c₂ μ (by rwa [List.append_assoc, List.singleton_append] at h))
      simp only [List.append_assoc, List.singleton_append] at hseg
      refine ⟨_, .inl (.ans (.inr m) n) :: callMoves seg,
        K.wait s a c' c m (hc.of_prefix (List.prefix_append _ _)) hP h₁,
        .cons (.reply s a c (.inr m) n) hseg, ?_, okV_cons.2 ⟨trivial, okV_callMoves ?_⟩⟩
      · simp [visMove, vis_callMoves, h₂]
      · exact fun y hy => (ok_append.1 hc).2 y (.tail _ hy)
  | ret s a c' b s' hb =>
    rcases hb with ⟨c, hc, hok, rfl⟩ | ⟨hd, -⟩
    · cases hK
      exact ⟨_, [.inr (.ans a (.inl b))], K.run s a _ c hok (reach_of_beh hc) rfl,
        .cons (.ret s a c b s' hc) (.nil _), rfl, okV_cons.2 ⟨trivial, OkV.nil⟩⟩
    · cases hd
  | trap s a c' hb =>
    rcases hb with ⟨c, hc, hok, rfl⟩ | ⟨hd, -⟩
    · cases hK
      exact ⟨_, [.inr (.ans a (.inr PUnit.unit))], K.run s a _ c hok (reach_of_beh hc) rfl,
        .cons (.trap s a c hc) (.nil _), rfl, okV_cons.2 ⟨trivial, OkV.nil⟩⟩
    · cases hd
  | deadAsk a =>
    cases hK
    exact ⟨_, [.inr (.ask a)], K.dead, .cons (.deadAsk a) (.nil _), rfl,
      okV_cons.2 ⟨trivial, OkV.nil⟩⟩

/-- **Backward**: a run of the linked automaton ending at a state related to `x'` is the visible
part of a run of `t` ending at `x'`. -/
theorem bwd {y y' : TSt F S A} {q : List (Move F (sig1 A B))}
    (h : TRun (hostLinkS R t).1 (satP (hostLinkS R t)) y q y') {x' : TSt (E ⊕ₛ F) S A}
    (hK : K R t y' x') :
    ∃ x p, K R t y x ∧ TRun t.1 (satP t) x p x' ∧ vis p = q ∧ OkV R p := by
  induction h with
  | nil => exact ⟨x', [], hK, .nil _, rfl, OkV.nil⟩
  | cons hs _ ih =>
    obtain ⟨x₁, p', hK₁, hp', hv', hok'⟩ := ih hK
    obtain ⟨x, ph, hK₀, hph, hvh, hokh⟩ := bwd_step hs hK₁
    exact ⟨x, ph ++ p', hK₀, hph.append hp', by simp [hvh, hv'],
      okV_append.2 ⟨hokh, hok'⟩⟩

theorem exK_step {y y₁ : TSt F S A} {o : Move F (sig1 A B)}
    (h : TStep (hostLinkS R t).1 (satP (hostLinkS R t)) y o y₁) {x : TSt (E ⊕ₛ F) S A}
    (hK : K R t y x) : ∃ x₁, K R t y₁ x₁ := by
  cases h with
  | ask s a => exact ⟨_, K.run s a [] [] Ok.nil reach_nil rfl⟩
  | call s a c' m hP =>
    obtain ⟨c, hc, hok, rfl⟩ := satP_hostLinkS hP
    exact ⟨_, K.wait s a _ c m hok hc rfl⟩
  | reply s a c' m n =>
    cases hK with
    | wait _ _ _ c _ hok hP he =>
      exact ⟨_, K.run s a _ (c ++ [⟨.inr m, n⟩]) (ok_inr hok) (reach_snoc hP)
        (by rw [fCalls_append, he]; rfl)⟩
  | ret s a c' b s' => exact ⟨_, K.idle s'⟩
  | trap => exact ⟨_, K.dead⟩
  | deadAsk a => exact ⟨_, K.stuck a⟩

/-- Every state reached by the linked automaton is related to a state of `t`. -/
theorem exK {y y' : TSt F S A} {q : List (Move F (sig1 A B))}
    (h : TRun (hostLinkS R t).1 (satP (hostLinkS R t)) y q y') {x : TSt (E ⊕ₛ F) S A}
    (hK : K R t y x) : ∃ x', K R t y' x' := by
  induction h generalizing x with
  | nil => exact ⟨x, hK⟩
  | cons hs _ ih =>
    obtain ⟨x₁, hK₁⟩ := exK_step hs hK
    exact ih hK₁

/-! ## The finite plays -/

section Session

variable {t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- A run of `t` from `s₀` gives a play of the session and its host moves a play of the host
beside copycat. -/
theorem interaction_of_run {p : List (Move (E ⊕ₛ F) (sig1 A (B ⊕ PUnit.{u + 1})))}
    {x : TSt (E ⊕ₛ F) S A} (hp : TRun t.1 (satP t) (.idle s₀) p x) (hok : OkV R p) :
    p.map relMove ∈ (threadS t s₀).toStrategy ∧
      hmv (p.map relMove) ∈ (hostCopy F R).toStrategy ∧
      Zip (hmv (p.map relMove)) (p.map relMove) ((vis p).map relMove) := by
  refine ⟨⟨p, ⟨x, hp⟩, rfl⟩, ⟨_, hrun_hmv (relPath hp.pos) (okV_map_relMove.2 hok)⟩, ?_⟩
  rw [← vis_map_relMove]; exact zip_hmv _

/-- A play of the session with allowed host answers, seen from the linked session. -/
theorem fwd_play {v : List (Move (E ⊕ₛ F) (sig1 A B))} (hv : v ∈ (threadS t s₀).toStrategy)
    (hok : OkV R v) : ∃ p x y, TRun t.1 (satP t) (.idle s₀) p x ∧ p.map relMove = v ∧
      TRun (hostLinkS R t).1 (satP (hostLinkS R t)) (.idle s₀) (vis p) y ∧ J R t x y ∧
      vis v = (vis p).map relMove ∧ Path .idle v (relPos x.pos) := by
  obtain ⟨p, ⟨x, hx⟩, rfl⟩ := hv
  obtain ⟨y, hy, hJ⟩ := fwd hx (okV_map_relMove.1 hok) (J.idle s₀)
  exact ⟨p, x, y, hx, rfl, hy, hJ, vis_map_relMove p, relPath hx.pos⟩

/-- **The finite plays of the composite are those of the linked session.** -/
theorem mem_comp_iff {q : List (Move F (sig1 A B))} :
    q ∈ ((hostCopy F R).comp (threadS t s₀)).toStrategy ↔
      q ∈ (threadS (hostLinkS R t) s₀).toStrategy := by
  constructor
  · rintro ⟨sH, ⟨h, hrH⟩, v, hv, hz⟩
    obtain ⟨p, x, hT, rfl⟩ : ∃ p x, TRun t.1 (satP t) (.idle s₀) p x ∧ p.map relMove = v := by
      obtain ⟨p, ⟨x, hx⟩, hp⟩ := hv; exact ⟨p, x, hx, hp⟩
    obtain ⟨hc, hok, he⟩ := zip_fwd hz hrH (relPath hT.pos) Compat.idle
    obtain ⟨y, hy, hJ⟩ := fwd hT (okV_map_relMove.1 hok) (J.idle s₀)
    simp only [aOf, bOf, List.nil_append] at he
    rw [vis_map_relMove] at he
    cases h with
    | ansF m n =>
      generalize hX : relPos x.pos = X at hc
      cases hc with
      | ansF g _ _ =>
        cases x <;> simp [TSt.pos, relPos] at hX
        rename_i s g' c μ
        obtain ⟨rfl, rfl⟩ := hX
        cases hJ with
        | waitF _ _ _ _ hcok =>
          simp only [List.append_nil] at he
          exact ⟨_, ⟨_, hy.append (.cons (.reply s g _ m n) (.nil _))⟩,
            by rw [he, List.map_append]; rfl⟩
    | idle =>
      simp only [List.append_nil] at he
      exact ⟨_, ⟨_, hy⟩, he.symm⟩
    | waitE m =>
      simp only [List.append_nil] at he
      exact ⟨_, ⟨_, hy⟩, he.symm⟩
    | waitF m =>
      simp only [List.append_nil] at he
      exact ⟨_, ⟨_, hy⟩, he.symm⟩
    | askF m =>
      simp only [List.append_nil] at he
      exact (threadS (hostLinkS R t) s₀).toStrategy.of_prefix ⟨_, ⟨_, hy⟩, rfl⟩
        ⟨_, he⟩
  · rintro ⟨q₁, ⟨y, hy⟩, rfl⟩
    obtain ⟨x', hK'⟩ := exK hy (K.idle s₀)
    obtain ⟨x, p, hK, hT, rfl, hok⟩ := bwd hy hK'
    cases hK
    obtain ⟨hv, hh, hz⟩ := interaction_of_run hT hok
    exact ⟨_, hh, _, hv, hz⟩

end Session

end Silmaril.Proofs.Games.Abstract.SessionHost
