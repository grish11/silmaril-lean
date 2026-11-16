module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Hist
public import Silmaril.Proofs.Games.Abstract.SessionLink.Parse
public import Silmaril.Proofs.Games.Abstract.SessionLink.Div
import Mathlib.Data.List.Basic

/-!
# Linking sessions: stages of an infinite interaction (proofs)

An infinite interaction of the server and client sessions, in which the client plays a productive
stream inside one round (`stage_clientStream`) or the server plays a productive stream inside one
served call (`stage_serverStream`). At every late enough stage, the forward simulation with history
(`fwdH`), run on the coherent runs of both components, relates the visible play to the linked
automaton at a fixed store `σ`: the server's rounds before the current linked round are counted
by the hidden events (`upper_eq_lower`), and parsing the server's play against its coherent
infinite play (`parse`) pins the served rounds and their stores (`StoreDet`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-! ## Lists -/

theorem prefix_append_long {α : Type u} {X P Y : List α} (h : X <+: P ++ Y)
    (hl : P.length ≤ X.length) : ∃ X', X = P ++ X' ∧ X' <+: Y := by
  obtain ⟨Z, hZ⟩ := h
  rcases List.append_eq_append_iff.1 hZ with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · have : a' = [] := by simp at hl; exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], by simp, List.nil_prefix⟩
  · exact ⟨c', rfl, List.prefix_append _ _⟩

theorem length_lower_add_upper {F G : Sig.{u}} (s : List (Move F G)) :
    (lower s).length + (upper s).length = s.length := by
  induction s with
  | nil => rfl
  | cons o s ih => rcases o with e | e <;> simp <;> omega

theorem servedLog_streamTake (g : ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1})) (j : ℕ) :
    servedLog (streamTake g j) = (streamTake (fun k => (g k).2.1) j).flatten := by
  induction j with
  | zero => rfl
  | succ j ih => simp [streamTake_succ, servedLog_append, ih]

theorem served_streamTake (g : ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1})) (j : ℕ) :
    served (streamTake g j) = streamTake (fun k => (⟨(g k).1, (g k).2.2⟩ : Call (sig1 A B))) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [streamTake_succ, served_append, ih]

theorem streamTake_eq_iff {α : Type u} {f g : ℕ → α} {j : ℕ} :
    streamTake f j = streamTake g j ↔ ∀ k < j, f k = g k := by
  constructor
  · intro h k hk
    have := congrArg (fun l => l[k]?) h
    simpa [streamTake, List.getElem?_ofFn, hk] using this
  · intro h
    apply List.ext_getElem (by simp)
    intro k h₁ _
    simp only [streamTake, List.getElem_ofFn]
    exact h k (by simpa using h₁)

/-! ## The client's coherent runs inside its stream round -/

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- A play inside the client's stream round has an explicit run. -/
theorem client_stage {F₁ : Sig.{u}} {S₁ A₁ B₁ : Type u} {u : ObsTriple F₁ S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
    {s₀' s' : S₁} {rs_c : List (A₁ × List (Call F₁) × (B₁ ⊕ PUnit.{u + 1}))}
    {a' : A₁} {ω : ℕ → Call F₁} (hrc : Rounds u s₀' rs_c s') (hω : ω ∈ u.2.2 s' a')
    {q : List (Move F₁ (sig1 A₁ B₁))} {K : ℕ}
    (hq : q <+: sroundsMoves rs_c ++ .inr (.ask a') :: callMoves (streamTake ω K))
    (hl : (sroundsMoves rs_c : List (Move F₁ (sig1 A₁ B₁))).length < q.length) :
    ∃ j, (q = sroundsMoves rs_c ++ .inr (.ask a') :: callMoves (streamTake ω j) ∧
        SRun u (.idle s₀') q (.run s' a' (streamTake ω j))) ∨
      (q = sroundsMoves rs_c ++ .inr (.ask a') ::
          (callMoves (streamTake ω j) ++ [.inl (.ask (ω j).1)]) ∧
        SRun u (.idle s₀') q (.wait s' a' (streamTake ω j) (ω j).1)) := by
  obtain ⟨X, rfl, hX⟩ := prefix_append_long hq hl.le
  rcases X with _ | ⟨o, Q⟩
  · simp at hl
  obtain ⟨rfl, hQ⟩ := List.cons_prefix_cons.1 hX
  have hrun : ∀ j, SRun u (.idle s₀') (sroundsMoves rs_c ++ .inr (.ask a') ::
      callMoves (streamTake ω j)) (.run s' a' (streamTake ω j)) := fun j => by
    refine (run_rounds hrc).append (.cons (.ask _ _) ?_)
    simpa using run_callMoves (t := u) (s := s') (a := a') (streamTake ω j) (c₀ := [])
      (fun c m hc => by
        obtain ⟨j', rfl, rfl⟩ := callPre_streamTake (by simpa using hc)
        exact .inr (.inr (.inr ⟨ω, hω, j', rfl, rfl⟩)))
  obtain ⟨j, hj, h⟩ := prefix_callMoves hQ
  simp only [length_streamTake] at hj
  rcases h with rfl | ⟨hj', rfl⟩
  · refine ⟨j, .inl ⟨by rw [take_streamTake ω hj], ?_⟩⟩
    rw [take_streamTake ω hj]; exact hrun j
  · simp only [take_streamTake ω hj, getElem_streamTake ω (by simpa using hj')]
    refine ⟨j, .inr ⟨rfl, ?_⟩⟩
    have := (hrun j).append (.single (.call s' a' (streamTake ω j) (ω j).1
      (.inr (.inr (.inr ⟨ω, hω, j, rfl, rfl⟩)))))
    simpa using this

/-! ## Reading the forward simulation inside a client round -/

/-- Related states with the client running its round at `s'`: the linked round started at `σ`
with `σ.2 = s'`, and the server's play is its rounds and the served rounds. -/
theorem jh_run {s₀ : S} {w : List (Move E (sig1 A B))} {x : TSt E S A}
    {z : TSt E (S × S') A'} {s' : S'} {a' : A'} {d : List (Call (sig1 A B))}
    (hJ : JH t u s₀ w x (.run s' a' d) z) :
    ∃ R σ rs s, σ.2 = s' ∧ served rs = d ∧ Rounds t s₀ R σ.1 ∧ Rounds t σ.1 rs s ∧
      w = sroundsMoves (R ++ rs) ∧ z = .run σ a' (servedLog rs) := by
  generalize hy : (TSt.run s' a' d : TSt (sig1 A B) S' A') = y at hJ
  cases hJ with
  | run R σ a'' rs s hR₀ hR =>
    simp only [TSt.run.injEq] at hy
    obtain ⟨h₁, rfl, h₃⟩ := hy
    exact ⟨R, σ, rs, s, h₁.symm, h₃.symm, hR₀, hR, rfl, rfl⟩
  | idle => cases hy
  | call => cases hy
  | wait => cases hy
  | dead => cases hy
  | stuck => cases hy

/-- Related states with the client waiting on a call: the server runs the served call. -/
theorem jh_wait {s₀ : S} {w : List (Move E (sig1 A B))} {x : TSt E S A}
    {z : TSt E (S × S') A'} {s' : S'} {a' : A'} {d : List (Call (sig1 A B))} {a₀ : A}
    (hJ : JH t u s₀ w x (.wait s' a' d a₀) z) :
    ∃ R σ rs s c, σ.2 = s' ∧ served rs = d ∧ Rounds t s₀ R σ.1 ∧ Rounds t σ.1 rs s ∧
      (served rs, a₀) ∈ satP u σ.2 a' ∧
      ((w = sroundsMoves (R ++ rs) ++ .inr (.ask a₀) :: callMoves c ∧
          z = .run σ a' (servedLog rs ++ c)) ∨
        ∃ m, w = sroundsMoves (R ++ rs) ++ .inr (.ask a₀) :: (callMoves c ++ [.inl (.ask m)]) ∧
          z = .wait σ a' (servedLog rs ++ c) m) := by
  generalize hy : (TSt.wait s' a' d a₀ : TSt (sig1 A B) S' A') = y at hJ
  cases hJ with
  | call R σ a'' rs s a c hR₀ hR hu =>
    simp only [TSt.wait.injEq] at hy
    obtain ⟨h₁, rfl, h₃, rfl⟩ := hy
    exact ⟨R, σ, rs, s, c, h₁.symm, h₃.symm, hR₀, hR, hu, .inl ⟨rfl, rfl⟩⟩
  | wait R σ a'' rs s a c m hR₀ hR hu =>
    simp only [TSt.wait.injEq] at hy
    obtain ⟨h₁, rfl, h₃, rfl⟩ := hy
    exact ⟨R, σ, rs, s, c, h₁.symm, h₃.symm, hR₀, hR, hu, .inr ⟨m, rfl, rfl⟩⟩
  | idle => cases hy
  | run => cases hy
  | dead => cases hy
  | stuck => cases hy

/-- The partial round of the server, inside its coherent play: its calls are a prefix of the log
of the next coherent round. -/
theorem tail_in_round {f : ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1})} {K M : ℕ}
    {R'' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (hK : streamTake f K = streamTake f M ++ R'') {a : A} {c : List (Call E)}
    {T : List (Move E (sig1 A B))}
    (h : .inr (.ask a) :: (callMoves c ++ T) <+: sroundsMoves R'' ++ []) :
    c <+: (f M).2.1 ∧ ∀ m, T = [.inl (.ask m)] → CallPre c m (f M).2.1 := by
  rcases R'' with _ | ⟨r₀, R₀⟩
  · simp at h
  have hr₀ : r₀ = f M := by
    have hM : M < K := by
      have := congrArg List.length hK; simp at this; omega
    have := congrArg (fun l => l[M]?) hK
    simp [streamTake, hM] at this
    exact this.symm
  subst hr₀
  simp only [sroundsMoves_cons, List.append_nil, sroundMoves_append, List.cons_prefix_cons] at h
  exact callMoves_prefix_inv (fun _ _ h => by simp at h) h.2

/-- **Pinning the server**: the server's rounds before and inside the linked round, followed by a
partial round, inside a coherent infinite play of the server, are its first coherent rounds, at
their coherent stores. -/
theorem pin_server (htd : StoreDet t) {s₀ : S} {as : ℕ → A}
    {r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})} {st : ℕ → S} (hinf : InfRounds t s₀ as r st)
    {K N : ℕ} {R rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {σ₁ : S}
    {tail : List (Move E (sig1 A B))} (hR₀ : Rounds t s₀ R σ₁) (hlen : R.length = N)
    (hpre : sroundsMoves (R ++ rs) ++ tail <+: sroundsMoves (streamTake (fun i => (as i, r i)) K)) :
    σ₁ = st N ∧ rs = streamTake (fun k => (as (N + k), r (N + k))) rs.length ∧
      ∃ R'', streamTake (fun i => (as i, r i)) K =
          streamTake (fun i => (as i, r i)) (N + rs.length) ++ R'' ∧
        tail <+: sroundsMoves R'' ++ [] := by
  obtain ⟨R'', hK, htail⟩ := parse (R := R ++ rs) (T := tail) (T' := [])
    (fun _ h => by simp at h) (by rw [List.append_nil]; exact hpre)
  have hle : N + rs.length ≤ K := by
    have := congrArg List.length hK; simp at this; omega
  have htake : R ++ rs = streamTake (fun i => (as i, r i)) (N + rs.length) := by
    rw [← take_streamTake _ hle, hK, List.take_left' (by simp [hlen])]
  have htake' := htake
  rw [streamTake_add] at htake'
  obtain ⟨rfl, hrs⟩ := List.append_inj htake' (by simp [hlen])
  refine ⟨rounds_det htd hR₀ (InfRounds.rounds hinf N), hrs, R'', ?_, htail⟩
  rw [hK, htake]

/-- **A stage of an interaction in which the client streams inside its round**, the server
playing a coherent infinite play. The linked automaton runs the round at `(st N, s')`, where `N`
counts the client's calls before the round, the coherent server rounds `N + k` serve the client's
calls `ω k`, and the visible log is the log of the served rounds then a prefix of the next. -/
theorem stage_clientStream (hnt : NoPlainTrap t) (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀'))
    {rs_c : List (A' × List (Call (sig1 A B)) × (B' ⊕ PUnit.{u + 1}))} {s' : S'} {a' : A'}
    {ω : ℕ → Call (sig1 A B)} (hrc : Rounds u s₀' rs_c s') (hω : ω ∈ u.2.2 s' a')
    (hlimt : i.t.lim = streamPlay (sroundsMoves rs_c) a' ω)
    {as : ℕ → A} {r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})} {st : ℕ → S}
    (hinf : InfRounds t s₀ as r st) (hlims : i.s.lim = sroundsPlay as r) {N : ℕ}
    (hN : (lower (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B')))).length = 2 * N)
    {n : ℕ}
    (hn : (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B'))).length < (i.t n).length) :
    ∃ j c z, SRun (linkS t u) (.idle (s₀, s₀')) (i.p n) z ∧
      (∀ k < j, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k) ∧
      (i.t n).length ≤
        (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B'))).length + 2 * j + 2 ∧
      ((z = .run (st N, s') a' (logTake (fun k => (r (N + k)).1) j ++ c) ∧
          c <+: (r (N + j)).1) ∨
        ∃ m, z = .wait (st N, s') a' (logTake (fun k => (r (N + k)).1) j ++ c) m ∧
          CallPre c m (r (N + j)).1) := by
  obtain ⟨K, hK⟩ : i.t n ∈ streamPlay (sroundsMoves rs_c) a' ω := hlimt ▸ Chain.mem_lim_self _ n
  obtain ⟨K', hK'⟩ : i.s n ∈ sroundsPlay as r := hlims ▸ Chain.mem_lim_self _ n
  have hsr := run_rounds (t := t) (InfRounds.rounds hinf K')
  obtain ⟨Z, hZ⟩ := hK'
  change i.s n ++ Z = sroundsMoves (streamTake (fun i => (as i, r i)) K') at hZ
  rw [← hZ] at hsr
  obtain ⟨x, hx, -⟩ := hsr.of_append
  have hcount := congrArg List.length (upper_eq_lower (i.zip n))
  have hagree : ∀ {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {j},
      served rs = streamTake ω j →
      rs = streamTake (fun k => (as (N + k), r (N + k))) rs.length →
      rs.length = j ∧ ∀ k < j, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k := by
    intro rs j hs hrs
    have hl : rs.length = j := by simpa [served] using congrArg List.length hs
    refine ⟨hl, ?_⟩
    rw [hrs, hl, served_streamTake] at hs
    exact streamTake_eq_iff.1 hs
  have hlog : ∀ {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))},
      rs = streamTake (fun k => (as (N + k), r (N + k))) rs.length →
      servedLog rs = logTake (fun k => (r (N + k)).1) rs.length := by
    intro rs hrs
    rw [hrs, servedLog_streamTake, length_streamTake]; rfl
  obtain ⟨j, ⟨hq, hy⟩ | ⟨hq, hy⟩⟩ := client_stage hrc hω hK hn
  · obtain ⟨z, hzr, hJ⟩ := fwdH hnt (i.zip n) (JH.idle (u := u) [] s₀ s₀' (.nil _)) hx hy
    simp only [sroundsMoves_nil, List.nil_append] at hJ
    obtain ⟨R, σ, rs, s, hσ, hs, hR₀, hR, hw, rfl⟩ := jh_run hJ
    rw [hw] at hcount hZ
    rw [hq] at hcount
    have hlenrs : rs.length = j := by simpa [served] using congrArg List.length hs
    have hRN : R.length = N := by
      simp [upper_append, length_upper_sroundsMoves, lower_append, hN] at hcount
      omega
    obtain ⟨hσ₁, hrs, -⟩ := pin_server (tail := []) htd hinf hR₀ hRN
      ⟨Z, by rw [List.append_nil]; exact hZ⟩
    obtain ⟨-, hag⟩ := hagree hs hrs
    have hσeq : σ = (st N, s') := Prod.ext hσ₁ hσ
    subst hσeq
    refine ⟨j, [], _, hzr, hag, by rw [hq]; simp [length_callMoves]; omega, .inl ⟨?_, List.nil_prefix⟩⟩
    rw [List.append_nil, hlog hrs, hlenrs]
  · obtain ⟨z, hzr, hJ⟩ := fwdH hnt (i.zip n) (JH.idle (u := u) [] s₀ s₀' (.nil _)) hx hy
    simp only [sroundsMoves_nil, List.nil_append] at hJ
    obtain ⟨R, σ, rs, s, c, hσ, hs, hR₀, hR, -, hw⟩ := jh_wait hJ
    have hlenrs : rs.length = j := by simpa [served] using congrArg List.length hs
    have key : ∀ (T : List (Move E (sig1 A B))), (T = [] ∨ ∃ m, T = [.inl (.ask m)]) →
        i.s n = sroundsMoves (R ++ rs) ++ .inr (.ask (ω j).1) :: (callMoves c ++ T) →
        σ = (st N, s') ∧ (∀ k < j, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k) ∧
          servedLog rs = logTake (fun k => (r (N + k)).1) j ∧ c <+: (r (N + j)).1 ∧
          ∀ m, T = [.inl (.ask m)] → CallPre c m (r (N + j)).1 := by
      intro T hT hw
      rw [hw] at hcount hZ
      rw [hq] at hcount
      have hRN : R.length = N := by
        rcases hT with rfl | ⟨m, rfl⟩ <;>
        · simp [upper_append, length_upper_sroundsMoves, lower_append, hN] at hcount
          omega
      obtain ⟨hσ₁, hrs, R'', hK'', htail⟩ := pin_server htd hinf hR₀ hRN ⟨Z, hZ⟩
      obtain ⟨-, hag⟩ := hagree hs hrs
      rw [hlenrs] at hK''
      have := tail_in_round (f := fun i => (as i, r i)) hK'' htail
      exact ⟨Prod.ext hσ₁ hσ, hag, by rw [hlog hrs, hlenrs], this.1, this.2⟩
    rcases hw with ⟨hw, rfl⟩ | ⟨m, hw, rfl⟩
    · obtain ⟨rfl, hag, hlg, hc, -⟩ := key [] (.inl rfl) (by simpa using hw)
      refine ⟨j, c, _, hzr, hag, by rw [hq]; simp [length_callMoves]; omega, .inl ⟨by rw [hlg], hc⟩⟩
    · obtain ⟨rfl, hag, hlg, -, hc⟩ := key [.inl (.ask m)] (.inr ⟨m, rfl⟩) hw
      exact ⟨j, c, _, hzr, hag, by rw [hq]; simp [length_callMoves]; omega, .inr ⟨m, by rw [hlg], hc m rfl⟩⟩

/-! ## The server streams inside a served call -/

/-- Related states with the server running a served call. -/
theorem jh_srv {s₀ : S} {w : List (Move E (sig1 A B))} {y : TSt (sig1 A B) S' A'}
    {z : TSt E (S × S') A'} {s : S} {a : A} {c : List (Call E)} {T : List (Move E (sig1 A B))}
    {x : TSt E S A} (hx : (x = .run s a c ∧ T = []) ∨ ∃ m, x = .wait s a c m ∧ T = [.inl (.ask m)])
    (hJ : JH t u s₀ w x y z) :
    ∃ R σ a' rs, y = .wait σ.2 a' (served rs) a ∧ Rounds t s₀ R σ.1 ∧ Rounds t σ.1 rs s ∧
      (served rs, a) ∈ satP u σ.2 a' ∧
      w = sroundsMoves (R ++ rs) ++ .inr (.ask a) :: (callMoves c ++ T) ∧
      ((T = [] ∧ z = .run σ a' (servedLog rs ++ c)) ∨
        ∃ m, T = [.inl (.ask m)] ∧ z = .wait σ a' (servedLog rs ++ c) m) := by
  cases hJ with
  | call R σ a' rs s₂ a₂ c₂ hR₀ hR hu =>
    rcases hx with ⟨hx, rfl⟩ | ⟨m, hx, -⟩
    · simp only [TSt.run.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ⟨R, σ, a', rs, rfl, hR₀, hR, hu, by simp, .inl ⟨rfl, rfl⟩⟩
    · cases hx
  | wait R σ a' rs s₂ a₂ c₂ m₂ hR₀ hR hu =>
    rcases hx with ⟨hx, -⟩ | ⟨m, hx, rfl⟩
    · cases hx
    · simp only [TSt.wait.injEq] at hx
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨R, σ, a', rs, rfl, hR₀, hR, hu, rfl, .inr ⟨m₂, rfl, rfl⟩⟩
  | idle => rcases hx with ⟨hx, -⟩ | ⟨m, hx, -⟩ <;> cases hx
  | run => rcases hx with ⟨hx, -⟩ | ⟨m, hx, -⟩ <;> cases hx
  | dead => rcases hx with ⟨hx, -⟩ | ⟨m, hx, -⟩ <;> cases hx
  | stuck => rcases hx with ⟨hx, -⟩ | ⟨m, hx, -⟩ <;> cases hx

/-- Completed rounds with equal moves are equal. -/
theorem sroundsMoves_inj {R R' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : (sroundsMoves R : List (Move E (sig1 A B))) = sroundsMoves R') : R = R' := by
  obtain ⟨R₁, hR₁, -⟩ := parse (R := R) (R' := R') (T := []) (T' := [])
    (fun _ h => by simp at h) (by rw [h]; exact List.prefix_refl _)
  obtain ⟨R₂, hR₂, -⟩ := parse (R := R') (R' := R) (T := []) (T' := [])
    (fun _ h => by simp at h) (by rw [h]; exact List.prefix_refl _)
  have h1 := congrArg List.length hR₁
  have h2 := congrArg List.length hR₂
  simp only [List.length_append] at h1 h2
  rw [hR₁, List.eq_nil_of_length_eq_zero (by omega : R₁.length = 0), List.append_nil]

/-- **A stage of an interaction in which the server streams inside a served call.** The client
waits on the served call; the linked round started at `σ`, after the server rounds `R`, and the
served rounds `rs` complete the server's rounds `R_s` before its stream. -/
theorem stage_serverStream (hnt : NoPlainTrap t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀'))
    {R_s : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {s₁ : S} {a_s : A} {ω_t : ℕ → Call E}
    (hRs : Rounds t s₀ R_s s₁) (hωt : ω_t ∈ t.2.2 s₁ a_s)
    (hlims : i.s.lim = streamPlay (sroundsMoves R_s) a_s ω_t) {n : ℕ}
    (hn : (sroundsMoves R_s : List (Move E (sig1 A B))).length < (i.s n).length)
    {y : TSt (sig1 A B) S' A'} (hy : SRun u (.idle s₀') (i.t n) y) :
    ∃ R rs σ a' j z, y = .wait σ.2 a' (served rs) a_s ∧ R_s = R ++ rs ∧ Rounds t s₀ R σ.1 ∧
      Rounds t σ.1 rs s₁ ∧ (served rs, a_s) ∈ satP u σ.2 a' ∧
      SRun (linkS t u) (.idle (s₀, s₀')) (i.p n) z ∧
      (i.s n).length ≤ (sroundsMoves R_s : List (Move E (sig1 A B))).length + 2 * j + 2 ∧
      (z = .run σ a' (servedLog rs ++ streamTake ω_t j) ∨
        z = .wait σ a' (servedLog rs ++ streamTake ω_t j) (ω_t j).1) := by
  obtain ⟨K, hK⟩ : i.s n ∈ streamPlay (sroundsMoves R_s) a_s ω_t := hlims ▸ Chain.mem_lim_self _ n
  obtain ⟨j, ⟨hq, hx⟩ | ⟨hq, hx⟩⟩ := client_stage hRs hωt hK hn
  · obtain ⟨z, hzr, hJ⟩ := fwdH hnt (i.zip n) (JH.idle (u := u) [] s₀ s₀' (.nil _)) hx hy
    simp only [sroundsMoves_nil, List.nil_append] at hJ
    obtain ⟨R, σ, a', rs, rfl, hR₀, hR, hu, hw, hz⟩ := jh_srv (T := []) (.inl ⟨rfl, rfl⟩) hJ
    rw [hq, List.append_nil] at hw
    have hRs' : R_s = R ++ rs := sroundsMoves_inj (List.append_cancel_right hw)
    rcases hz with ⟨-, rfl⟩ | ⟨m, hm, -⟩
    · exact ⟨R, rs, σ, a', j, _, rfl, hRs', hR₀, hR, hu, hzr,
        by rw [hq]; simp [length_callMoves]; omega, .inl rfl⟩
    · cases hm
  · obtain ⟨z, hzr, hJ⟩ := fwdH hnt (i.zip n) (JH.idle (u := u) [] s₀ s₀' (.nil _)) hx hy
    simp only [sroundsMoves_nil, List.nil_append] at hJ
    obtain ⟨R, σ, a', rs, rfl, hR₀, hR, hu, hw, hz⟩ :=
      jh_srv (T := [.inl (.ask (ω_t j).1)]) (.inr ⟨_, rfl, rfl⟩) hJ
    rw [hq] at hw
    have hRs' : R_s = R ++ rs := sroundsMoves_inj (List.append_cancel_right hw)
    rcases hz with ⟨hm, -⟩ | ⟨m, hm, rfl⟩
    · cases hm
    · simp only [List.cons.injEq, Sum.inl.injEq, Ev.ask.injEq, and_true] at hm
      subst hm
      exact ⟨R, rs, σ, a', j, _, rfl, hRs', hR₀, hR, hu, hzr,
        by rw [hq]; simp [length_callMoves]; omega, .inr rfl⟩

end Silmaril.Proofs.Games.Abstract.SessionLink
