module

public import Silmaril.Games.Abstract.StratHost.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Mathlib.Data.List.Basic

/-!
# Linking a play object with a relational host (proofs)

`(hostD R).comp (toDStrat t) = toDStrat (linkT R t)`.

* `fwd`: an interaction of a host play and a play of `toDStrat t` has a visible part accepted by
  the closed automaton of `linkT R t`, with the states related by `J`;
* `bwd`: conversely, a run of the closed automaton is the visible part of such an interaction;
* `zip_vis`, `zip_length`, `zip_mem`: with no lower interface, the visible part of an interaction
  is the upper projection of the upper play, the host moves only in synchrony, and every answer
  of the upper play comes from the host;
* divergence from chatter: the upper limit is an infinite play of `toDStrat t`; it cannot
  complete infinitely many rounds (the visible part would grow), so it is a productive stream
  after finitely many rounds, every answer allowed by the host.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratHost

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Lists of moves -/

section Moves

variable {F : Sig.{u}}

@[simp] theorem callMoves_nil : (callMoves ([] : List (Call E)) : List (Move E F)) = [] := rfl

@[simp] theorem callMoves_cons (x : Call E) (c : List (Call E)) :
    (callMoves (x :: c) : List (Move E F)) =
      .inl (.ask x.1) :: .inl (.ans x.1 x.2) :: callMoves c :=
  rfl

@[simp] theorem callMoves_append (c d : List (Call E)) :
    (callMoves (c ++ d) : List (Move E F)) = callMoves c ++ callMoves d := by
  simp [callMoves]

theorem length_callMoves (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

@[simp] theorem upper_callMoves (c : List (Call E)) :
    upper (callMoves c : List (Move E F)) = [] := by
  induction c with
  | nil => rfl
  | cons x c ih => exact ih

theorem inl_ans_mem_callMoves {c : List (Call E)} {x : Call E} (hx : x ∈ c) :
    (.inl (.ans x.1 x.2) : Move E F) ∈ callMoves c := by
  induction c with
  | nil => cases hx
  | cons y c ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · simp [ih hx]

/-- The host moves answering a log. -/
def hostMoves (c : List (Call E)) : List (Move Sig.empty.{u} E) :=
  c.flatMap fun x => [.inr (.ask x.1), .inr (.ans x.1 x.2)]

@[simp] theorem hostMoves_nil : hostMoves ([] : List (Call E)) = [] := rfl

@[simp] theorem hostMoves_cons (x : Call E) (c : List (Call E)) :
    hostMoves (x :: c) = .inr (.ask x.1) :: .inr (.ans x.1 x.2) :: hostMoves c := rfl

@[simp] theorem hostMoves_append (c d : List (Call E)) :
    hostMoves (c ++ d) = hostMoves c ++ hostMoves d := by
  simp [hostMoves]

theorem length_hostMoves (c : List (Call E)) : (hostMoves c).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

theorem streamTake_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

@[simp] theorem length_streamTake {α : Type u} (ω : ℕ → α) (k : ℕ) :
    (streamTake ω k).length = k := by
  simp [streamTake]

theorem streamTake_prefix {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω k <+: streamTake ω (k + 1) := by
  rw [streamTake_succ]; exact List.prefix_append _ _

@[simp] theorem upper_cons_inl {F G : Sig.{u}} (b : Ev F) (t : List (Move F G)) :
    upper (.inl b :: t) = upper t := rfl

@[simp] theorem upper_cons_inr {F G : Sig.{u}} (c : Ev G) (t : List (Move F G)) :
    upper (.inr c :: t) = c :: upper t := rfl

end Moves

/-! ## Zips with no lower interface -/

section Zip

variable {G : Sig.{u}}

theorem zip_hostMoves {s : List (Move Sig.empty.{u} E)} {t : List (Move E G)}
    {p : List (Move Sig.empty.{u} G)} (c : List (Call E)) (h : Zip s t p) :
    Zip (hostMoves c ++ s) (callMoves c ++ t) p := by
  induction c with
  | nil => exact h
  | cons x c ih => exact .sync _ (.sync _ ih)

theorem zip_append {α β γ : Type u} {s₁ s₂ : List (α ⊕ β)} {t₁ t₂ : List (β ⊕ γ)}
    {p₁ p₂ : List (α ⊕ γ)} (h₁ : Zip s₁ t₁ p₁) (h₂ : Zip s₂ t₂ p₂) :
    Zip (s₁ ++ s₂) (t₁ ++ t₂) (p₁ ++ p₂) := by
  induction h₁ with
  | nil => exact h₂
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

theorem zip_calls (c : List (Call E)) :
    Zip (hostMoves c) (callMoves c : List (Move E G)) ([] : List (Move Sig.empty.{u} G)) := by
  simpa using zip_hostMoves (G := G) c .nil

/-- With no lower interface, the visible part is the upper projection of the upper play. -/
theorem zip_vis {s : List (Move Sig.empty.{u} E)} {t : List (Move E G)}
    {p : List (Move Sig.empty.{u} G)} (h : Zip s t p) : p = (upper t).map Sum.inr := by
  induction h with
  | nil => rfl
  | left a _ _ => cases a with | ask m => exact m.elim | ans m _ => exact m.elim
  | right c _ ih => simp [ih]
  | sync b _ ih => simpa using ih

/-- With no lower interface, the host moves only in synchrony. -/
theorem zip_length {s : List (Move Sig.empty.{u} E)} {t : List (Move E G)}
    {p : List (Move Sig.empty.{u} G)} (h : Zip s t p) : s.length ≤ t.length := by
  induction h with
  | nil => exact le_rfl
  | left a _ _ => cases a with | ask m => exact m.elim | ans m _ => exact m.elim
  | right c _ ih => simp; omega
  | sync b _ ih => simpa using ih

/-- Every lower move of the upper play is a host move. -/
theorem zip_mem {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p : List (α ⊕ γ)}
    (h : Zip s t p) {b : β} (hb : .inl b ∈ t) : .inr b ∈ s := by
  induction h with
  | nil => cases hb
  | left a _ ih => exact .tail _ (ih hb)
  | right c _ ih => exact ih (by simpa using hb)
  | sync b' _ ih =>
    rcases List.mem_cons.1 hb with h | h
    · cases h; exact .head _
    · exact .tail _ (ih h)

/-- Positions of `E ↠ G` seen from `F ↠ G` when the lower interface is hidden. -/
def proj {F : Sig.{u}} : Pos E G → Pos F G
  | .idle => .idle
  | .run q => .run q
  | .wait q _ => .run q

theorem path_upper {F : Sig.{u}} {x y : Pos E G} {t : List (Move E G)} (h : Path x t y) :
    Path (proj x : Pos F G) ((upper t).map Sum.inr) (proj y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    cases hs with
    | ask q => exact .cons (.ask q) ih
    | call q m => simpa [proj] using ih
    | reply q m n => simpa [proj] using ih
    | ret q r => exact .cons (.ret q r) ih

end Zip

/-! ## The host strategy -/

section Host

variable {R : HostRel E}

theorem hostOk_nil : HostOk R [] := fun _ _ h => nomatch h

theorem hostOk_append {s s' : List (Move Sig.empty.{u} E)} (h : HostOk R s) (h' : HostOk R s') :
    HostOk R (s ++ s') := fun m n hm => (List.mem_append.1 hm).elim (h m n) (h' m n)

theorem hostOk_tail {o : Move Sig.empty.{u} E} {s : List (Move Sig.empty.{u} E)}
    (h : HostOk R (o :: s)) : HostOk R s := fun m n hm => h m n (.tail _ hm)

theorem hostOk_hostMoves {c : List (Call E)} (hc : R.Consistent c) : HostOk R (hostMoves c) := by
  induction c with
  | nil => exact hostOk_nil
  | cons x c ih =>
    intro m n hm
    simp only [hostMoves_cons, List.mem_cons] at hm
    rcases hm with h | h | h
    · cases h
    · cases h; exact hc _ (.head _)
    · exact ih (fun y hy => hc y (.tail _ hy)) m n h

theorem hostOk_ask {m : E.Op} : HostOk R [(.inr (.ask m) : Move Sig.empty.{u} E)] :=
  fun _ _ h => by cases List.mem_singleton.1 h

theorem path_hostMoves (c : List (Call E)) :
    Path (.idle : Pos Sig.empty.{u} E) (hostMoves c) .idle := by
  induction c with
  | nil => exact .nil _
  | cons x c ih => exact .cons (.ask _) (.cons (.ret _ _) ih)

theorem consistent_append {c d : List (Call E)} (hc : R.Consistent c) (hd : R.Consistent d) :
    R.Consistent (c ++ d) := fun x hx => (List.mem_append.1 hx).elim (hc x) (hd x)

end Host

/-! ## Runs of the automaton -/

section Runs

variable {f : AFun E S A B} {P : Pending E S A}

theorem ARun.nil_eq {x y : St E S A} (h : ARun f P x [] y) : x = y := by
  cases h; rfl

theorem run_callMoves {q : S × A} (d : List (Call E)) {c₀ : List (Call E)}
    (hd : ∀ c m, CallPre c m (c₀ ++ d) → (c, m) ∈ P q.1 q.2) :
    ARun f P (.run q c₀) (callMoves d) (.run q (c₀ ++ d)) := by
  induction d generalizing c₀ with
  | nil => simpa using ARun.nil _
  | cons x d ih =>
    have h := ih (c₀ := c₀ ++ [x]) (by simpa using hd)
    simp only [List.append_assoc, List.singleton_append] at h
    exact .cons (.call q c₀ x.1 (hd c₀ x.1 ⟨x.2, d, rfl⟩)) (.cons (.reply q c₀ x.1 x.2) h)

/-- A run ending in a running state ends with the question. -/
theorem run_split {u : List (Move E (funSig S A B))} {q : S × A}
    (h : ARun f P .idle u (.run q [])) :
    ∃ pre, u = pre ++ [.inr (.ask q)] ∧ ARun f P .idle pre .idle := by
  rcases List.eq_nil_or_concat u with rfl | ⟨pre, o, rfl⟩
  · cases h
  · rw [List.concat_eq_append] at h ⊢
    obtain ⟨z, h₁, h₂⟩ := h.of_append
    cases h₂ with
    | cons hst hn =>
      have he := ARun.nil_eq hn
      cases hst with
      | ask => cases he; exact ⟨pre, rfl, h₁⟩
      | call => cases he
      | reply _ c _ _ => simp at he
      | ret => cases he

end Runs

/-! ## The forward direction -/

variable {R : HostRel E} {t : ObsTriple E S A B}

/-- Related states of the upper automaton, the host and the closed automaton. -/
inductive J (R : HostRel E) (t : ObsTriple E S A B) :
    St E S A → Pos Sig.empty.{u} E → St Sig.empty.{u} S A → Prop
  | idle : J R t .idle .idle .idle
  | run (q : S × A) (c : List (Call E)) : R.Consistent c → J R t (.run q c) .idle (.run q [])
  | wait (q : S × A) (c : List (Call E)) (m : E.Op) : R.Consistent c →
      (c, m) ∈ satP t q.1 q.2 →
      J R t (.wait q c m) (.run m) (.run q [])

/-- **Forward**: the visible part of an interaction is a run of the closed automaton. -/
theorem fwd {s : List (Move Sig.empty.{u} E)} {v : List (Move E (funSig S A B))}
    {p : List (Move Sig.empty.{u} (funSig S A B))} (hz : Zip s v p) :
    ∀ {x x' h h' y}, J R t x h y → ARun t.1 (satP t) x v x' → Path h s h' → HostOk R s →
      ∃ y', ARun (linkT R t).1 (satP (linkT R t)) y p y' ∧ J R t x' h' y' := by
  induction hz with
  | nil =>
    intro x x' h h' y hJ hv hs _
    cases hv; cases hs
    exact ⟨y, .nil _, hJ⟩
  | left a _ _ => cases a with | ask m => exact m.elim | ans m _ => exact m.elim
  | right c _ ih =>
    intro x x' h h' y hJ hv hs hok
    cases hv with
    | cons hst hr =>
      cases hst with
      | ask q =>
        cases hJ
        obtain ⟨y', hy', hJ'⟩ := ih (J.run q [] (fun _ h => nomatch h)) hr hs hok
        exact ⟨y', .cons (.ask q) hy', hJ'⟩
      | ret q c₀ r hb =>
        cases hJ with
        | run _ _ hc =>
          obtain ⟨y', hy', hJ'⟩ := ih J.idle hr hs hok
          exact ⟨y', .cons (.ret q [] r (.inl ⟨c₀, hb, hc⟩)) hy', hJ'⟩
  | sync b _ ih =>
    intro x x' h h' y hJ hv hs hok
    cases hv with
    | cons hst hr =>
      cases hs with
      | cons hh hs =>
        cases hst with
        | call q c m hP =>
          cases hJ with
          | run _ _ hc =>
            cases hh
            exact ih (J.wait q c m hc hP) hr hs (hostOk_tail hok)
        | reply q c m n =>
          cases hJ with
          | wait _ _ _ hc _ =>
            cases hh
            have hn : R m (.answer n) := hok m n (.head _)
            exact ih (J.run q _ (consistent_append hc fun x hx => by
              cases List.mem_singleton.1 hx; exact hn)) hr hs (hostOk_tail hok)

/-- A play of the composite is a play of the linked triple. -/
theorem fwd_play {s : List (Move Sig.empty.{u} E)} {v : List (Move E (funSig S A B))}
    {p : List (Move Sig.empty.{u} (funSig S A B))} (hz : Zip s v p) (hs : s ∈ hostS R)
    (hv : v ∈ (toDStrat t).toStrategy) :
    ∃ x h y, ARun t.1 (satP t) .idle v x ∧ Path .idle s h ∧
      ARun (linkT R t).1 (satP (linkT R t)) .idle p y ∧ J R t x h y := by
  obtain ⟨x, hx⟩ := hv
  obtain ⟨h, hh⟩ := hs.1
  obtain ⟨y, hy, hJ⟩ := fwd hz J.idle hx hh hs.2
  exact ⟨x, h, y, hx, hh, hy, hJ⟩

/-! ## The backward direction -/

/-- Related states of the closed and the upper automaton, the host idle. -/
inductive K : St Sig.empty.{u} S A → St E S A → Prop
  | idle : K .idle .idle
  | run (q : S × A) : K (.run q []) (.run q [])

/-- **Backward**: a run of the closed automaton is the visible part of an interaction. -/
theorem bwd {p : List (Move Sig.empty.{u} (funSig S A B))} {y y' : St Sig.empty.{u} S A}
    (hp : ARun (linkT R t).1 (satP (linkT R t)) y p y') :
    ∀ {x}, K y x → ∃ s v x', Zip s v p ∧ Path .idle s .idle ∧ HostOk R s ∧
      ARun t.1 (satP t) x v x' ∧ K y' x' := by
  induction hp with
  | nil => intro x hK; exact ⟨[], [], x, .nil, .nil _, hostOk_nil, .nil _, hK⟩
  | cons hst _ ih =>
    intro x hK
    cases hst with
    | ask q =>
      cases hK
      obtain ⟨s, v, x', hz, hs, hok, hv, hK'⟩ := ih (K.run q)
      exact ⟨s, _, x', .right _ hz, hs, hok, .cons (.ask q) hv, hK'⟩
    | call _ _ m => exact m.elim
    | reply _ _ m => exact m.elim
    | ret q c r hm =>
      cases hK with
      | run =>
        rcases hm with ⟨cs, hb, hc⟩ | ⟨hd, -⟩
        · obtain ⟨s, v, x', hz, hs, hok, hv, hK'⟩ := ih K.idle
          refine ⟨hostMoves cs ++ s, callMoves cs ++ .inr (.ans q r) :: v, x',
            zip_hostMoves cs (.right _ hz), (path_hostMoves cs).append hs,
            hostOk_append (hostOk_hostMoves hc) hok, ?_, hK'⟩
          have hr := run_callMoves (f := t.1) (P := satP t) (q := q) cs (c₀ := [])
            fun c m h => .inr (.inr (.inl ⟨cs, _, hb, by simpa using h⟩))
          simp only [List.nil_append] at hr
          exact hr.append (.cons (.ret q cs r hb) hv)
        · cases r <;> cases hd

/-! ## Finite plays -/

theorem mem_plays_iff {p : List (Move Sig.empty.{u} (funSig S A B))} :
    p ∈ ((hostD R).comp (toDStrat t)).toStrategy ↔ p ∈ (toDStrat (linkT R t)).toStrategy := by
  constructor
  · rintro ⟨s, hs, v, hv, hz⟩
    obtain ⟨-, -, y, -, -, hy, -⟩ := fwd_play hz hs hv
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨s, v, x', hz, hs, hok, hv, -⟩ := bwd hy K.idle
    exact ⟨s, ⟨⟨_, hs⟩, hok⟩, v, ⟨x', hv⟩, hz⟩

/-! ## Divergence -/

/-- **Divergence from chatter**: an infinite interaction with a constant visible part is a
productive stream of `t` after finitely many rounds, every answer allowed. -/
theorem chatter (i : DStrategy.InfInteraction (hostD R) (toDStrat t))
    {p : List (Move Sig.empty.{u} (funSig S A B))} (hi : ∀ n, i.p n = p) :
    p ∈ (toDStrat (linkT R t)).div := by
  have hvis : ∀ n, p = (upper (i.t n)).map Sum.inr := fun n => (hi n) ▸ zip_vis (i.zip n)
  obtain ⟨g, hg⟩ : ∃ g, Path .idle p (.run g) := DStrategy.compDiv_run (.inr ⟨i, hi⟩)
  have hu : i.t.Unbounded := fun k => by
    obtain ⟨n, hn⟩ := i.unbounded (2 * k)
    exact ⟨n, by have := zip_length (i.zip n); omega⟩
  obtain ⟨-, -, hcase⟩ := i.lim_t hu
  rcases hcase with ⟨pre, q, ω, -, hω, hI⟩ | hB
  · have hL : ∀ k, ∃ n, pre ++ .inr (.ask q) :: callMoves (streamTake ω k) <+: i.t n :=
      fun k => by
        have h : pre ++ .inr (.ask q) :: callMoves (streamTake ω k) ∈ i.t.lim :=
          hI ▸ ⟨k, List.prefix_refl _⟩
        exact h
    have hall : ∀ k, R (ω k).1 (.answer (ω k).2) := fun k => by
      obtain ⟨n, hn⟩ := hL (k + 1)
      have hmem : (.inl (.ans (ω k).1 (ω k).2) : Move E (funSig S A B)) ∈ i.t n :=
        hn.subset (List.mem_append_right _ (List.mem_cons_of_mem _
          (inl_ans_mem_callMoves (by rw [streamTake_succ]; simp))))
      exact (i.mem_s n).2 _ _ (zip_mem (i.zip n) hmem)
    obtain ⟨n, r, hr⟩ := hL 0
    obtain ⟨K, hK⟩ : i.t n ∈ streamPlay pre q ω := hI ▸ Chain.mem_lim_self _ n
    simp only [streamTake, List.ofFn_zero, callMoves_nil] at hr
    rw [← hr, List.append_assoc] at hK
    have hr' : upper r = [] := by
      have h := (List.prefix_append_right_inj _).1 hK
      rw [List.singleton_append, List.cons_prefix_cons] at h
      have h := h.2.filterMap Sum.getRight?
      change upper r <+: upper (callMoves _) at h
      rw [upper_callMoves] at h
      exact List.prefix_nil.1 h
    have hp : p = (upper pre).map Sum.inr ++ [.inr (.ask q)] := by
      rw [hvis n, ← hr]; simp [upper, List.filterMap_append] at hr' ⊢; simp [hr']
    obtain ⟨-, -, y, -, -, hy, -⟩ := fwd_play (i.zip n) (i.mem_s n) (i.mem_t n)
    rw [hi n] at hy
    have hy' := hy
    rw [hp] at hy'
    obtain ⟨z, -, h₂⟩ := hy'.of_append
    cases h₂ with
    | cons hst hn =>
      cases hst
      cases ARun.nil_eq hn
      exact ⟨q, [], hy, .inr ⟨rfl, .inr ⟨ω, hω, hall⟩⟩⟩
  · exfalso
    obtain ⟨x', ⟨n, hn⟩, h0, hx'⟩ := hB _ (Chain.mem_lim_self _ 0)
    have h1 : upper (i.t 0) <+: upper x' := h0.filterMap _
    have h3 : upper (i.t n) = upper (i.t 0) :=
      List.map_injective_iff.2 Sum.inr_injective ((hvis n).symm.trans (hvis 0))
    have h2 : upper x' <+: upper (i.t 0) := h3 ▸ hn.filterMap _
    have h4 : upper x' = upper (i.t 0) := h2.eq_of_length (le_antisymm h2.length_le h1.length_le)
    have hp : Path (.idle : Pos Sig.empty.{u} (funSig S A B)) p .idle := by
      have := path_upper (F := Sig.empty.{u}) hx'.pos
      rwa [h4, ← hvis 0] at this
    cases hp.det hg

theorem div_fwd {p : List (Move Sig.empty.{u} (funSig S A B))}
    (hp : p ∈ ((hostD R).comp (toDStrat t)).div) : p ∈ (toDStrat (linkT R t)).div := by
  rcases hp with ⟨s, v, hz, ⟨⟨hs, m, hm, hdv⟩, hv⟩ | ⟨hs, hv⟩⟩ | ⟨i, hi⟩
  · obtain ⟨x, h, y, -, hh, hy, hJ⟩ := fwd_play hz hs hv
    cases hh.det hm
    cases hJ with
    | wait q c _ hc hP =>
      exact ⟨q, [], hy, .inr ⟨rfl, .inl ⟨c, m, ⟨hP, hc, .inr hdv⟩, hdv⟩⟩⟩
  · obtain ⟨q, c, hvq, hcd⟩ := hv
    obtain ⟨x, h, y, hx, -, hy, hJ⟩ :=
      fwd_play hz hs ((toDStrat t).div_mem (s := v) ⟨q, c, hvq, hcd⟩)
    cases hx.det hvq
    cases hJ with
    | run _ _ hc => exact ⟨q, [], hy, .inl ⟨c, hcd, hc⟩⟩
  · exact chatter i hi

theorem div_bwd {p : List (Move Sig.empty.{u} (funSig S A B))}
    (hp : p ∈ (toDStrat (linkT R t)).div) : p ∈ ((hostD R).comp (toDStrat t)).div := by
  obtain ⟨q, c, hp, hm⟩ := hp
  obtain ⟨s, v, x', hz, hs, hok, hv, hK⟩ := bwd hp K.idle
  cases hK
  rcases hm with ⟨cs, hb, hc⟩ | ⟨-, ⟨c', m, ⟨hP, hc, -⟩, hdv⟩ | ⟨ω, hω, hall⟩⟩
  · have hr := run_callMoves (f := t.1) (P := satP t) (q := q) cs (c₀ := [])
      fun c m h => .inr (.inr (.inl ⟨cs, _, hb, by simpa using h⟩))
    simp only [List.nil_append] at hr
    have hz' := zip_append hz (zip_calls (G := funSig S A B) cs)
    rw [List.append_nil] at hz'
    exact .inl ⟨_, _, hz', .inr ⟨⟨⟨_, hs.append (path_hostMoves cs)⟩,
      hostOk_append hok (hostOk_hostMoves hc)⟩, q, cs, hv.append hr, hb⟩⟩
  · have hr := run_callMoves (f := t.1) (P := satP t) (q := q) c' (c₀ := [])
      fun c₁ m₁ h => satP_prefix hP (by simpa using h)
    simp only [List.nil_append] at hr
    have hz' := zip_append (zip_append hz (zip_calls (G := funSig S A B) c'))
      (Zip.sync (Ev.ask m) Zip.nil : Zip [(.inr (.ask m) : Move Sig.empty.{u} E)]
        [(.inl (.ask m) : Move E (funSig S A B))] [])
    simp only [List.append_nil] at hz'
    have hpath : Path .idle (s ++ hostMoves c' ++ [.inr (.ask m)]) (.run m) :=
      (hs.append (path_hostMoves c')).append (Path.single (Step.ask m))
    exact .inl ⟨_, _, hz', .inl ⟨⟨⟨⟨_, hpath⟩, hostOk_append (hostOk_append hok
      (hostOk_hostMoves hc)) hostOk_ask⟩, m, hpath, hdv⟩,
      ⟨_, (hv.append hr).append (.cons (.call q c' m hP) (.nil _))⟩⟩⟩
  · obtain ⟨pre, rfl, hpre⟩ := run_split hv
    have hsp : streamPlay pre q ω ∈ (toDStrat t).inf := streamPlay_mem hpre hω
    have hzn : ∀ n, Zip (s ++ hostMoves (streamTake ω n))
        (pre ++ .inr (.ask q) :: callMoves (streamTake ω n)) p := fun n => by
      have := zip_append hz (zip_calls (G := funSig S A B) (streamTake ω n))
      simpa using this
    have hms : ∀ n, s ++ hostMoves (streamTake ω n) ∈ (hostD R).toStrategy := fun n =>
      ⟨⟨_, hs.append (path_hostMoves _)⟩,
        hostOk_append hok (hostOk_hostMoves (hostObsInf_consistent ⟨hω, hall⟩ n))⟩
    have mono_s : Chain.Mono fun n => s ++ hostMoves (streamTake ω n) := fun n =>
      ⟨hostMoves [ω n], by simp [streamTake_succ]⟩
    have mono_t : Chain.Mono fun n => pre ++ .inr (.ask q) :: callMoves (streamTake ω n) :=
      fun n => ⟨callMoves [ω n], by simp [streamTake_succ]⟩
    let i : DStrategy.InfInteraction (hostD R) (toDStrat t) :=
      { s := fun n => s ++ hostMoves (streamTake ω n)
        t := fun n => pre ++ .inr (.ask q) :: callMoves (streamTake ω n)
        p := fun _ => p
        zip := hzn
        mem_s := hms
        mem_t := fun n => (toDStrat t).inf_sub hsp ⟨n, List.prefix_refl _⟩
        mono_s := mono_s
        mono_t := mono_t
        mono_p := fun _ => List.prefix_refl _
        unbounded := fun k => ⟨k, by simp [length_callMoves]; omega⟩
        lim_s := fun hu => ⟨Chain.isInfPlay_lim mono_s hu,
          fun _ ⟨n, hx⟩ => (hostS R).of_prefix (hms n) hx⟩
        lim_t := fun _ => hsp }
    exact .inr ⟨i, fun _ => rfl⟩

/-! ## Infinite plays -/

theorem inf_fwd {I : Set (List (Move Sig.empty.{u} (funSig S A B)))}
    (hI : I ∈ ((hostD R).comp (toDStrat t)).inf) : I ∈ (toDStrat (linkT R t)).inf := by
  obtain ⟨i, hu, rfl⟩ := hI
  have hplay : ∀ n, ∃ y, ARun (linkT R t).1 (satP (linkT R t)) .idle (i.p n) y := fun n => by
    obtain ⟨-, -, y, -, -, hy, -⟩ := fwd_play (i.zip n) (i.mem_s n) (i.mem_t n)
    exact ⟨y, hy⟩
  refine ⟨Chain.isInfPlay_lim i.mono_p hu,
    fun x ⟨n, hx⟩ => (toDStrat (linkT R t)).toStrategy.of_prefix (hplay n) hx, .inr ?_⟩
  rintro x ⟨n, hx⟩
  obtain ⟨m, hnm, hm⟩ := i.mono_p.unbounded_ge hu (x.length + 2) n
  obtain ⟨y, hy⟩ := hplay m
  have hxm : x <+: i.p m := hx.trans (i.mono_p.le hnm)
  cases y with
  | idle => exact ⟨i.p m, Chain.mem_lim_self _ m, hxm, hy⟩
  | run q c =>
    cases c with
    | nil =>
      obtain ⟨pre, hpre, hpi⟩ := run_split hy
      refine ⟨pre, ⟨m, hpre ▸ List.prefix_append _ _⟩, ?_, hpi⟩
      rw [hpre] at hxm hm
      rcases List.prefix_concat_iff.1 hxm with h | h
      · exfalso; rw [h, List.length_append] at hm; simp at hm; omega
      · exact h
    | cons a _ => exact a.1.elim
  | wait q c m => exact m.elim

/-- Interactions of host and upper plays, all idle, whose visible part is a member of `I`. -/
def Stage (R : HostRel E) (t : ObsTriple E S A B)
    (I : Set (List (Move Sig.empty.{u} (funSig S A B)))) : Type u :=
  {w : List (Move Sig.empty.{u} E) × List (Move E (funSig S A B)) ×
      List (Move Sig.empty.{u} (funSig S A B)) //
    Zip w.1 w.2.1 w.2.2 ∧ Path .idle w.1 .idle ∧ HostOk R w.1 ∧
      ARun t.1 (satP t) .idle w.2.1 .idle ∧
      ARun (linkT R t).1 (satP (linkT R t)) .idle w.2.2 .idle ∧ w.2.2 ∈ I}

theorem stage_step {I : Set (List (Move Sig.empty.{u} (funSig S A B)))} (hI : IsInfPlay I)
    (hB : ∀ x ∈ I, ∃ x' ∈ I, x <+: x' ∧
      ARun (linkT R t).1 (satP (linkT R t)) .idle x' .idle)
    (w : Stage R t I) :
    ∃ w' : Stage R t I, w.1.1 <+: w'.1.1 ∧ w.1.2.1 <+: w'.1.2.1 ∧ w.1.2.2 <+: w'.1.2.2 ∧
      w.1.2.2.length < w'.1.2.2.length := by
  obtain ⟨⟨s, v, p⟩, hz, hs, hok, hv, hp, hpI⟩ := w
  dsimp only at hz hs hok hv hp hpI ⊢
  obtain ⟨z, hz₀, hzl⟩ := hI.unbounded (p.length + 1)
  obtain ⟨z', hz', hzz', hz'r⟩ := hB z hz₀
  obtain ⟨d, rfl⟩ := hI.prefix_of_length_le hpI hz' (by have := hzz'.length_le; omega)
  obtain ⟨y₀, h₁, h₂⟩ := hz'r.of_append
  cases h₁.det hp
  obtain ⟨sd, vd, x', hzd, hsd, hokd, hvd, hK⟩ := bwd h₂ K.idle
  cases hK
  have := hzz'.length_le
  exact ⟨⟨(s ++ sd, v ++ vd, p ++ d), zip_append hz hzd, hs.append hsd, hostOk_append hok hokd,
    hv.append hvd, hz'r, hz'⟩, List.prefix_append _ _, List.prefix_append _ _,
    List.prefix_append _ _, by simp only [List.length_append] at this ⊢; omega⟩

/-- The chain of stages, each strictly longer than the last. -/
noncomputable def stageSeq {I : Set (List (Move Sig.empty.{u} (funSig S A B)))}
    (hI : IsInfPlay I)
    (hB : ∀ x ∈ I, ∃ x' ∈ I, x <+: x' ∧
      ARun (linkT R t).1 (satP (linkT R t)) .idle x' .idle)
    (w₀ : Stage R t I) : ℕ → Stage R t I
  | 0 => w₀
  | n + 1 => Classical.choose (stage_step hI hB (stageSeq hI hB w₀ n))

theorem inf_bwd {I : Set (List (Move Sig.empty.{u} (funSig S A B)))}
    (hI : I ∈ (toDStrat (linkT R t)).inf) : I ∈ ((hostD R).comp (toDStrat t)).inf := by
  obtain ⟨hII, -, hcase⟩ := hI
  rcases hcase with ⟨_, _, _, _, hω, _⟩ | hB
  · exact absurd hω (Set.notMem_empty _)
  have hnil : [] ∈ I := by
    obtain ⟨z, hz, -⟩ := hII.unbounded 0
    exact hII.of_prefix hz List.nil_prefix
  let W := stageSeq hII hB ⟨([], [], []), .nil, .nil _, hostOk_nil, .nil _, .nil _, hnil⟩
  have hstep : ∀ n, (W n).1.1 <+: (W (n + 1)).1.1 ∧ (W n).1.2.1 <+: (W (n + 1)).1.2.1 ∧
      (W n).1.2.2 <+: (W (n + 1)).1.2.2 ∧ (W n).1.2.2.length < (W (n + 1)).1.2.2.length :=
    fun n => Classical.choose_spec (stage_step hII hB (W n))
  have hlen : ∀ n, n ≤ (W n).1.2.2.length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := (hstep n).2.2.2; omega
  have hpv : ∀ n, (W n).1.2.2.length ≤ (W n).1.2.1.length := fun n => by
    rw [zip_vis (W n).2.1, List.length_map]; exact List.length_filterMap_le _ _
  have mono_s : Chain.Mono fun n => (W n).1.1 := fun n => (hstep n).1
  have mono_t : Chain.Mono fun n => (W n).1.2.1 := fun n => (hstep n).2.1
  have hmt : ∀ n, (W n).1.2.1 ∈ (toDStrat t).toStrategy := fun n => ⟨_, (W n).2.2.2.2.1⟩
  let i : DStrategy.InfInteraction (hostD R) (toDStrat t) :=
    { s := fun n => (W n).1.1
      t := fun n => (W n).1.2.1
      p := fun n => (W n).1.2.2
      zip := fun n => (W n).2.1
      mem_s := fun n => ⟨⟨_, (W n).2.2.1⟩, (W n).2.2.2.1⟩
      mem_t := hmt
      mono_s := mono_s
      mono_t := mono_t
      mono_p := fun n => (hstep n).2.2.1
      unbounded := fun k => ⟨k, by have := hlen k; have := hpv k; omega⟩
      lim_s := fun hu => ⟨Chain.isInfPlay_lim mono_s hu,
        fun _ ⟨n, hx⟩ => (hostS R).of_prefix ⟨⟨_, (W n).2.2.1⟩, (W n).2.2.2.1⟩ hx⟩
      lim_t := fun hu => ⟨Chain.isInfPlay_lim mono_t hu,
        fun _ ⟨n, hx⟩ => (toDStrat t).toStrategy.of_prefix (hmt n) hx,
        .inr fun _ ⟨n, hx⟩ => ⟨_, Chain.mem_lim_self _ n, hx, (W n).2.2.2.2.1⟩⟩ }
  refine ⟨i, fun k => ⟨k, hlen k⟩,
    Set.ext fun x => ⟨fun hx => ?_, fun ⟨n, hx⟩ => ?_⟩⟩
  · exact ⟨x.length, hII.prefix_of_length_le hx (W _).2.2.2.2.2.2 (hlen _)⟩
  · exact hII.of_prefix (W n).2.2.2.2.2.2 hx

/-- **Linking is interaction plus hiding.** -/
theorem comp_hostD_toDStrat : (hostD R).comp (toDStrat t) = toDStrat (linkT R t) :=
  DStrategy.ext (Strategy.ext fun _ => mem_plays_iff) (Set.ext fun _ => ⟨div_fwd, div_bwd⟩)
    (Set.ext fun _ => ⟨inf_fwd, inf_bwd⟩)

end Silmaril.Proofs.Games.Abstract.StratHost
