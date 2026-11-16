module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.BuildA
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Chatter
public import Silmaril.Wasm.Component.DWiringLaws.Thms
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.DPair.Thms

/-!
# Infinite plays through handler layers

The infinite versions of the forward constructions of `Build` (`hc_pend`, `hb_pend`,
`rplay_pair_inr`) and of the complete rounds (`cplay_comp_ofHandler`, `cplay_ofHandler_comp`),
for streams of rounds:

* `rch cl g X`: complete rounds `cl`, then `g` pending after the first `n` lower calls of the
  stream `X` (an infinite pending round, as the importer's chatter); `cch X`: the first `n`
  rounds of the stream `X` (infinitely many complete rounds, as the exporter serving them).
* A handler on top (`inf_top_pend`, `inf_top_cpl`), a one-call handler below (`inf_below_pend`,
  `inf_below_cpl`, through `DStrategy.inf_ofHandler_comp`) and the right component of a pairing
  (`inf_pair_pend`, `inf_pair_cpl`, through `DStrategy.inf_map_liftR`) send the limit of the
  stream below to the limit of the stream above, an infinite play of the composite.

On top, the handler forwards a pending question by one fixed play (the lower calls pass through),
or forwards every round by its own run; below, it serves the lower calls one by one. The chains
are built round by round, so they increase by construction.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference

local notation "GChain" => Silmaril.Games.Chain

/-! ## Chains -/

section Chains

theorem lim_image {α β : Type} (f : α → β) (c : GChain α) :
    List.map f '' c.lim = Silmaril.Games.Chain.lim (fun n => (c n).map f) := by
  ext q
  constructor
  · rintro ⟨p, ⟨n, hp⟩, rfl⟩
    exact ⟨n, prefix_map f hp⟩
  · rintro ⟨n, t, ht⟩
    refine ⟨(c n).take q.length, ⟨n, List.take_prefix _ _⟩, ?_⟩
    have ht' : q ++ t = (c n).map f := ht
    rw [List.map_take, ← ht']
    simp

theorem streamTake_zero {α : Type} (ω : ℕ → α) : streamTake ω 0 = [] := rfl

theorem zip_len {α β γ : Type} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) : p.length ≤ s.length + t.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | left _ _ ih => simp only [List.length_cons]; omega
  | right _ _ ih => simp only [List.length_cons]; omega
  | sync _ _ ih => simp only [List.length_cons]; omega

/-- A stream of lists, concatenated. -/
def catC {α : Type} (T : ℕ → List α) : GChain α := fun n => (streamTake T n).flatten

theorem flatten_streamTake_mono {α : Type} (T : ℕ → List α) : (catC T).Mono := fun n =>
  flatten_prefix (streamTake_prefix T (Nat.le_succ n))

theorem flatten_streamTake_succ {α : Type} (T : ℕ → List α) (n : ℕ) :
    (streamTake T (n + 1)).flatten = (streamTake T n).flatten ++ T n := by
  rw [streamTake_snoc, List.flatten_append, List.flatten_singleton]

end Chains

variable {E F G : Sig.{0}}

section Plays

theorem cplay_app : ∀ (l l' : List (CRound E F)), cplay (l ++ l') = cplay l ++ cplay l'
  | [], _ => rfl
  | r :: l, l' => by
    show .inr (.ask r.q) :: (callMoves r.cs ++ (.inr (.ans r.q r.a) :: cplay (l ++ l'))) =
      .inr (.ask r.q) :: (callMoves r.cs ++ (.inr (.ans r.q r.a) :: cplay l)) ++ cplay l'
    rw [cplay_app l l', List.cons_append, List.append_assoc, List.cons_append]

theorem length_cplay_ge : ∀ l : List (CRound E F), l.length ≤ (cplay l).length
  | [] => Nat.le_refl _
  | r :: l => by
    have := length_cplay_ge l
    simp only [cplay, List.length_cons, List.length_append]
    omega

theorem rplay_app (cl : List (CRound E F)) (g : F.Op) (A B : List (Round E)) :
    rplay cl g (A ++ B) = rplay cl g A ++ callMoves B := by
  simp only [rplay, callMoves_app, List.cons_append, List.append_assoc]

theorem callMoves_liftR {F₁ F₂ : Sig.{0}} :
    ∀ cs : List (Round E),
      (callMoves cs : List (Move E (F₁ ⊕ₛ F₂))) = (callMoves cs).map (Split.liftR (F₁ := F₁))
  | [] => rfl
  | ⟨_, _⟩ :: cs => by
    show _ :: _ :: _ = _ :: _ :: _
    rw [callMoves_liftR cs]
    rfl

theorem cplay_inr {F₁ F₂ : Sig.{0}} :
    ∀ l : List (CRound E F₂),
      cplay (l.map (CRound.inr (F₁ := F₁))) = (cplay l).map (Split.liftR (F₁ := F₁))
  | [] => rfl
  | r :: l => by
    simp only [List.map_cons, cplay, List.map_append, List.map_cons, cplay_inr l,
      ← callMoves_liftR]
    rfl

theorem rplay_inr {F₁ F₂ : Sig.{0}} (l : List (CRound E F₂)) (g : F₂.Op) (cs : List (Round E)) :
    rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs =
      (rplay l g cs).map (Split.liftR (F₁ := F₁)) := by
  simp only [rplay, List.map_append, List.map_cons, cplay_inr, ← callMoves_liftR]
  rfl

end Plays

/-! ## The two kinds of streams -/

section Streams

/-- **An infinite pending round**: complete rounds `cl`, then `g` pending after the first `n`
lower calls of `X`. -/
def rch (cl : List (CRound E F)) (g : F.Op) (X : ℕ → Round E) : GChain (Move E F) :=
  fun n => rplay cl g (streamTake X n)

/-- **Infinitely many complete rounds**: the first `n` rounds of `X`. -/
def cch (X : ℕ → CRound E F) : GChain (Move E F) := fun n => cplay (streamTake X n)

theorem rch_succ (cl : List (CRound E F)) (g : F.Op) (X : ℕ → Round E) (n : ℕ) :
    rch cl g X (n + 1) = rch cl g X n ++ callMoves [X n] := by
  simp only [rch, streamTake_snoc, rplay_app]

theorem rch_mono (cl : List (CRound E F)) (g : F.Op) (X : ℕ → Round E) : (rch cl g X).Mono :=
  fun n => by
    rw [rch_succ]
    exact List.prefix_append _ _

theorem rch_len (cl : List (CRound E F)) (g : F.Op) (X : ℕ → Round E) (n : ℕ) :
    n ≤ (rch cl g X n).length := by
  simp only [rch, length_rplay, length_streamTake]
  omega

theorem rch_unbounded (cl : List (CRound E F)) (g : F.Op) (X : ℕ → Round E) :
    (rch cl g X).Unbounded := fun k => ⟨k, rch_len cl g X k⟩

theorem cch_succ (X : ℕ → CRound E F) (n : ℕ) : cch X (n + 1) = cch X n ++ cplay [X n] := by
  simp only [cch, streamTake_snoc, cplay_app]

theorem cch_mono (X : ℕ → CRound E F) : (cch X).Mono := fun n => by
  rw [cch_succ]
  exact List.prefix_append _ _

theorem cch_len (X : ℕ → CRound E F) (n : ℕ) : n ≤ (cch X n).length := by
  have := length_cplay_ge (streamTake X n)
  simp only [length_streamTake] at this
  exact this

theorem cch_unbounded (X : ℕ → CRound E F) : (cch X).Unbounded := fun k => ⟨k, cch_len X k⟩

theorem not_unbounded_const {α : Type} (t : List α) : ¬ (Silmaril.Games.Chain.Unbounded fun _ => t) := by
  intro hu
  obtain ⟨_, hn⟩ := hu (t.length + 1)
  exact absurd hn (Nat.not_succ_le_self _)

end Streams

/-! ## A handler on top -/

section Top

/-- `hc_pend`, with the handler's play independent of the pending lower calls. -/
theorem hc_pend_all {h : Handler F G} {up : List (CRound E G)} {low : List (CRound E F)}
    (H : HC h up low) {g : G.Op} {f : F.Op} {k : F.Ar f → Prog F (G.Ar g)}
    (hg : h g = .call f k) :
    ∃ t ∈ Strategy.ofHandler h, ∀ cs : List (Round E), Zip (rplay low f cs) t (rplay up g cs) := by
  obtain ⟨t, ht, hz⟩ := H.run
  refine ⟨t ++ [.inr (.ask g), .inl (.ask f)],
    Strategy.mem_ofHandler.mpr ⟨_, ht.append (.vis (.ask g) (.vis (.call hg) (.nil _)))⟩,
    fun cs => ?_⟩
  have h₀ := zip_calls_left (E := E) (F := F) (G := G) .nil cs
  simp only [List.append_nil] at h₀
  exact zip_append hz (.right _ (.sync _ h₀))

/-- **A handler on top of an infinite pending round**: it forwards the pending question by one
call, and the lower calls pass through. -/
theorem inf_top_pend {σ : DStrategy E F} {h : Handler F G} {up : List (CRound E G)}
    {low : List (CRound E F)} (H : HC h up low) {g : G.Op} {f : F.Op}
    {k : F.Ar f → Prog F (G.Ar g)} (hg : h g = .call f k) (X : ℕ → Round E)
    (hI : (rch low f X).lim ∈ σ.inf) :
    (rch up g X).lim ∈ (σ.comp (DStrategy.ofHandler h)).inf := by
  obtain ⟨t, ht, hz⟩ := hc_pend_all H hg
  exact ⟨{ s := rch low f X, t := fun _ => t, p := rch up g X, zip := fun n => hz _
           mem_s := fun n => σ.inf_sub hI (Silmaril.Games.Chain.mem_lim_self _ n), mem_t := fun _ => ht
           mono_s := rch_mono _ _ _, mono_t := fun _ => List.prefix_refl _
           mono_p := rch_mono _ _ _
           unbounded := fun k => ⟨k, (rch_len _ _ _ k).trans (Nat.le_add_right _ _)⟩
           lim_s := fun _ => hI
           lim_t := fun hu => absurd hu (not_unbounded_const t) },
    rch_unbounded _ _ _, rfl⟩

/-- **The runs of a handler, one after another, are an infinite play of it.** -/
theorem lim_runs_mem_inf {h : Handler F G} {T : ℕ → List (Move F G)}
    (hT : ∀ k, h.toReduction.toLTS.Run .idle (T k) .idle)
    (hu : (catC T).Unbounded) : (catC T).lim ∈ (DStrategy.ofHandler h).inf := by
  have hrun : ∀ n, h.toReduction.toLTS.Run .idle (streamTake T n).flatten .idle := by
    intro n
    induction n with
    | zero => exact .nil _
    | succ n ih =>
      rw [flatten_streamTake_succ]
      exact ih.append (hT n)
  let r : h.toReduction.toLTS.InfRun :=
    { st := fun _ => .idle
      tr := catC T
      st_zero := rfl
      tr_zero := rfl
      step := fun n => ⟨T n, flatten_streamTake_succ T n, hT n⟩ }
  exact DStrategy.lim_mem_inf_ofLTS r hu fun n =>
    (Strategy.ofHandler h).legal (Strategy.mem_ofHandler.mpr ⟨_, hrun n⟩)

/-- **A handler on top of infinitely many complete rounds**, forwarding each by its own run. -/
theorem inf_top_cpl {σ : DStrategy E F} {h : Handler F G} {U : ℕ → CRound E G}
    {W : ℕ → CRound E F} (H : ∀ k, HC h [U k] [W k]) (hI : (cch W).lim ∈ σ.inf) :
    (cch U).lim ∈ (σ.comp (DStrategy.ofHandler h)).inf := by
  choose T hT hz using fun k => (H k).run
  have hrun : ∀ n, h.toReduction.toLTS.Run .idle (streamTake T n).flatten .idle := by
    intro n
    induction n with
    | zero => exact .nil _
    | succ n ih =>
      rw [flatten_streamTake_succ]
      exact ih.append (hT n)
  have hzip : ∀ n, Zip (cch W n) (streamTake T n).flatten (cch U n) := by
    intro n
    induction n with
    | zero => exact .nil
    | succ n ih =>
      rw [cch_succ, cch_succ, flatten_streamTake_succ]
      exact zip_append ih (hz n)
  exact ⟨{ s := cch W, t := catC T, p := cch U, zip := hzip
           mem_s := fun n => σ.inf_sub hI (Silmaril.Games.Chain.mem_lim_self _ n)
           mem_t := fun n => Strategy.mem_ofHandler.mpr ⟨_, hrun n⟩
           mono_s := cch_mono _, mono_t := flatten_streamTake_mono T, mono_p := cch_mono _
           unbounded := fun k => ⟨k, (cch_len _ k).trans (Nat.le_add_right _ _)⟩
           lim_s := fun _ => hI
           lim_t := fun hu => lim_runs_mem_inf hT hu },
    cch_unbounded _, rfl⟩

end Top

/-! ## A handler below -/

section Below

/-- `hb_pend` along a stream of lower calls, served one by one. -/
theorem hb_pend_chain {h : Handler E F} {up : List (CRound F G)} {low : List (CRound E G)}
    (H : HB h up low) (g : G.Op) {X : ℕ → Round F} {Y : ℕ → Round E}
    (hXY : ∀ k, HRounds h [X k] [Y k]) :
    ∃ u : GChain (Move E F), (∀ n, u n ∈ Strategy.ofHandler h) ∧ u.Mono ∧
      ∀ n, Zip (u n) (rch up g X n) (rch low g Y n) := by
  obtain ⟨t₀, ht₀, hz₀⟩ := H.run
  choose T hT hz using fun k => (hXY k).serve (G := G)
  have hz' : ∀ k, Zip (T k) (callMoves [X k] : List (Move F G))
      (callMoves [Y k] : List (Move E G)) := fun k => by
    have := hz k (t₁ := []) (s₁ := []) (p₁ := []) .nil
    simpa only [List.append_nil] using this
  have hrun : ∀ n, h.toReduction.toLTS.Run .idle (streamTake T n).flatten .idle := by
    intro n
    induction n with
    | zero => exact .nil _
    | succ n ih =>
      rw [flatten_streamTake_succ]
      exact ih.append (hT n)
  have hzip : ∀ n, Zip (streamTake T n).flatten (callMoves (streamTake X n) : List (Move F G))
      (callMoves (streamTake Y n) : List (Move E G)) := by
    intro n
    induction n with
    | zero => exact .nil
    | succ n ih =>
      rw [flatten_streamTake_succ, streamTake_snoc, streamTake_snoc, callMoves_app,
        callMoves_app]
      exact zip_append ih (hz' n)
  refine ⟨fun n => t₀ ++ (streamTake T n).flatten,
    fun n => Strategy.mem_ofHandler.mpr ⟨_, ht₀.append (hrun n)⟩,
    fun n => (List.prefix_append_right_inj _).2 (flatten_streamTake_mono T n),
    fun n => zip_append hz₀ (.right _ (hzip n))⟩

/-- **A one-call handler below an infinite pending round**, serving its lower calls one by
one. -/
theorem inf_below_pend {h : Handler E F} (hh : OneCall h) {σ : DStrategy F G}
    {up : List (CRound F G)} {low : List (CRound E G)} (H : HB h up low) (g : G.Op)
    {X : ℕ → Round F} {Y : ℕ → Round E} (hXY : ∀ k, HRounds h [X k] [Y k])
    (hI : (rch up g X).lim ∈ σ.inf) :
    (rch low g Y).lim ∈ ((DStrategy.ofHandler h).comp σ).inf := by
  rw [DStrategy.inf_ofHandler_comp hh]
  obtain ⟨u, hu, hmu, hz⟩ := hb_pend_chain H g hXY
  exact ⟨_, hI, u, rch up g X, rch low g Y, hz, hu, fun m => Silmaril.Games.Chain.mem_lim_self _ m, hmu,
    rch_mono _ _ _, rch_mono _ _ _, rch_unbounded _ _ _, rfl⟩

/-- **A one-call handler below infinitely many complete rounds.** -/
theorem inf_below_cpl {h : Handler E F} (hh : OneCall h) {σ : DStrategy F G}
    {U : ℕ → CRound F G} {W : ℕ → CRound E G} (H : ∀ k, HB h [U k] [W k])
    (hI : (cch U).lim ∈ σ.inf) :
    (cch W).lim ∈ ((DStrategy.ofHandler h).comp σ).inf := by
  rw [DStrategy.inf_ofHandler_comp hh]
  choose T hT hz using fun k => (H k).run
  have hrun : ∀ n, h.toReduction.toLTS.Run .idle (streamTake T n).flatten .idle := by
    intro n
    induction n with
    | zero => exact .nil _
    | succ n ih =>
      rw [flatten_streamTake_succ]
      exact ih.append (hT n)
  have hzip : ∀ n, Zip (streamTake T n).flatten (cch U n) (cch W n) := by
    intro n
    induction n with
    | zero => exact .nil
    | succ n ih =>
      rw [cch_succ, cch_succ, flatten_streamTake_succ]
      exact zip_append ih (hz n)
  exact ⟨_, hI, catC T, cch U, cch W, hzip,
    fun n => Strategy.mem_ofHandler.mpr ⟨_, hrun n⟩, fun m => Silmaril.Games.Chain.mem_lim_self _ m,
    flatten_streamTake_mono T, cch_mono _, cch_mono _, cch_unbounded _, rfl⟩

end Below

/-! ## Pairing -/

section Pair

variable {F₁ F₂ : Sig.{0}}

/-- **The right component of a pairing, on an infinite pending round.** -/
theorem inf_pair_pend (σ₁ : DStrategy E F₁) {σ₂ : DStrategy E F₂} {l : List (CRound E F₂)}
    {g : F₂.Op} {X : ℕ → Round E} (h : (rch l g X).lim ∈ σ₂.inf) :
    (rch (l.map (CRound.inr (F₁ := F₁))) (.inr g) X).lim ∈ (σ₁.pair σ₂).inf := by
  have e : rch (l.map (CRound.inr (F₁ := F₁))) (.inr g) X =
      fun n => (rch l g X n).map (Split.liftR (F₁ := F₁)) :=
    funext fun n => rplay_inr l g _
  rw [e, ← lim_image]
  exact DStrategy.inf_map_liftR σ₁ h

/-- **The right component of a pairing, on infinitely many complete rounds.** -/
theorem inf_pair_cpl (σ₁ : DStrategy E F₁) {σ₂ : DStrategy E F₂} {X : ℕ → CRound E F₂}
    (h : (cch X).lim ∈ σ₂.inf) :
    (cch fun k => (X k).inr (F₁ := F₁)).lim ∈ (σ₁.pair σ₂).inf := by
  have e : cch (fun k => (X k).inr (F₁ := F₁)) =
      fun n => (cch X n).map (Split.liftR (F₁ := F₁)) := by
    funext n
    simp only [cch, ← cplay_inr]
    congr 1
    simp [streamTake, List.map_ofFn]
    rfl
  rw [e, ← lim_image]
  exact DStrategy.inf_map_liftR σ₁ h

end Pair

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
