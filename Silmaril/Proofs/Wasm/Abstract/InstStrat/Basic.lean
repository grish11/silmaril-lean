module

public import Silmaril.Wasm.Abstract.InstStrat.Defs
public import Silmaril.Games.Abstract.StratThread.Thms
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# Scalar Core 3.0 instances as threaded canonical play objects (proofs)

* `relabel_injective`, `map_relabel_callMoves`: the move map.
* Runs of the hidden transition system: `path_append`, `path_of_append`, `path_prefix`, and
  `path_reply` (after an import question every answer is accepted).
* `satP_sound`: the call prefixes of the instance triple are pending calls: the prefixes forced
  by finished behaviours, by pending calls and by productive streams are runs of the instance.
* `fwd`: a run of the threading automaton (`TRun`) is a relabelled run of the instance
  (invariant `FInv`, on the automaton state); no state is `dead` or `stuck`, since the triple
  has no `End.trap`.
* `bwd`: a run of the instance is matched by a run of the threading automaton on its
  relabelling (invariant `BInv`, on the hidden state).
* `mem_instThread`, `pull_instThread`, `reach_iff_reachableStore`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.InstStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread
open Silmaril.Wasm.Abstract.InstStrat
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

universe u

/-! ## The move map -/

theorem relabel_injective {E F : Sig.{u}} : Function.Injective (relabel (E := E) (F := F)) := by
  rintro (e | (q | ⟨q, r⟩)) (e' | (q' | ⟨q', r'⟩)) h <;> simp only [relabel] at h <;>
    cases h <;> rfl

theorem map_relabel_callMoves {E F : Sig.{u}} (c : List (Call E)) :
    (callMoves c : List (Move E F)).map relabel = callMoves c := by
  induction c with
  | nil => rfl
  | cons x c ih => simp only [callMoves, List.flatMap_cons] at ih ⊢; simp [ih, relabel]

theorem callMoves_concat {E F : Sig.{u}} (c : List (Call E)) (m : E.Op) (n : E.Ar m) :
    (callMoves (c ++ [⟨m, n⟩]) : List (Move E F)) =
      callMoves c ++ [.inl (.ask m), .inl (.ans m n)] := by
  simp [callMoves]

theorem callPre_prefix {E F : Sig.{u}} {c d : List (Call E)} {m : E.Op} (h : CallPre c m d)
    (L : List (Move E F)) :
    (callMoves c ++ [.inl (.ask m)] : List (Move E F)) <+: callMoves d ++ L := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨.inl (.ans m n) :: (callMoves c' ++ L), by simp [callMoves]⟩

/-! ## Runs of the instance -/

variable {I : ScalarInstance} {P : Profile}

theorem path_append {x y z : I.HState} {p q : List (Move I.E I.F)} (h₁ : I.Path P x p y)
    (h₂ : I.Path P y q z) : I.Path P x (p ++ q) z := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem path_of_append {x z : I.HState} {p q : List (Move I.E I.F)}
    (h : I.Path P x (p ++ q) z) : ∃ y, I.Path P x p y ∧ I.Path P y q z := by
  induction p generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o p ih =>
    cases h with
    | cons h hr => obtain ⟨y, h₁, h₂⟩ := ih hr; exact ⟨y, .cons h h₁, h₂⟩

theorem path_prefix {x z : I.HState} {p q : List (Move I.E I.F)} (h : I.Path P x q z)
    (hp : p <+: q) : ∃ y, I.Path P x p y := by
  obtain ⟨r, rfl⟩ := hp
  obtain ⟨y, hy, -⟩ := path_of_append h
  exact ⟨y, hy⟩

theorem path_single {x y : I.HState} {o : Move I.E I.F} (h : I.Trans P x o y) :
    I.Path P x [o] y := .cons h (.nil _)

theorem path_concat {x z : I.HState} {p : List (Move I.E I.F)} {o : Move I.E I.F}
    (h : I.Path P x (p ++ [o]) z) : ∃ y, I.Path P x p y ∧ I.Trans P y o z := by
  obtain ⟨y, hy, hz⟩ := path_of_append h
  cases hz with
  | cons h hn => cases hn; exact ⟨y, hy, h⟩

/-- After an import question, every answer is accepted. -/
theorem path_reply {x q : I.HState} {p : List (Move I.E I.F)} {m : I.E.Op}
    (h : I.Path P x (p ++ [.inl (.ask m)]) q) (n : I.E.Ar m) :
    ∃ q', I.Path P x (p ++ [.inl (.ask m), .inl (.ans m n)]) q' := by
  obtain ⟨y, hy, hq⟩ := path_concat h
  cases hq with
  | ucall run callout op =>
    exact ⟨_, by simpa using path_append h (path_single (.uret (I := I) (P := P) n))⟩

/-- Runs of a coherent productive stream. -/
theorem path_stream {s : Store Nat} {a : I.F.Op} {ω : ℕ → Call I.E} {x : ℕ → I.HState}
    (h0 : x 0 = .running a s (I.initThread a))
    (hx : ∀ k, ∃ y, I.Trans P (x k) (.inl (.ask (ω k).1)) y ∧
      I.Trans P y (.inl (.ans (ω k).1 (ω k).2)) (x (k + 1))) (k : ℕ) :
    I.Path P (.idle s) (.inr (.ask a) :: callMoves (streamTake ω k)) (x k) := by
  induction k with
  | zero =>
    have he : streamTake ω 0 = [] := by simp [streamTake]
    rw [he, h0]; exact .cons (.call s a) (.nil _)
  | succ k ih =>
    obtain ⟨y, h₁, h₂⟩ := hx k
    have he : streamTake ω (k + 1) = streamTake ω k ++ [⟨(ω k).1, (ω k).2⟩] := by
      simp only [streamTake]
      rw [List.ofFn_succ']
      simp
    rw [he, callMoves_concat]
    exact path_append ih (.cons h₁ (.cons h₂ (.nil _)))

/-! ## Call prefixes -/

/-- The call prefixes of the instance triple are runs of the instance. -/
theorem satP_sound {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} {m : I.E.Op}
    (h : (c, m) ∈ satP (instTriple I P) s a) :
    ∃ q, I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inl (.ask m)])) q := by
  rcases h with h | ⟨d, m', ⟨q, hq⟩, hc⟩ | ⟨d, e, he, hc⟩ | ⟨ω, ⟨x, h0, hx⟩, k, hk, hm⟩
  · exact h
  · exact path_prefix hq (List.cons_prefix_cons.2 ⟨rfl, callPre_prefix hc _⟩)
  · rcases he with ⟨v, s', -, hp⟩ | ⟨-, s', t, hp, -⟩
    · exact path_prefix hp (List.cons_prefix_cons.2 ⟨rfl, callPre_prefix hc _⟩)
    · have hc' := callPre_prefix (F := I.F) hc []
      rw [List.append_nil] at hc'
      exact path_prefix hp (List.cons_prefix_cons.2 ⟨rfl, hc'⟩)
  · obtain ⟨y, h₁, -⟩ := hx k
    obtain rfl : streamTake ω k = c := hk
    obtain rfl : (ω k).1 = m := hm
    exact ⟨y, path_append (path_stream h0 hx k) (path_single h₁)⟩

/-! ## From threading runs to instance runs -/

/-- The invariant of the forward simulation, on the state of the threading automaton. -/
def FInv (I : ScalarInstance) (P : Profile) (s₀ : Store Nat) (p' : List (Move I.E (tsig I.F))) :
    TSt I.E (Store Nat) I.F.Op → Prop
  | .idle s => ∃ p, p' = p.map relabel ∧ I.Path P (.idle s₀) p (.idle s)
  | .run s a c => ∃ p, p' = p.map relabel ++ (.inr (.ask a) :: callMoves c : List (Move I.E (tsig I.F))) ∧
      I.Path P (.idle s₀) p (.idle s) ∧ ∃ q, I.Path P (.idle s) (.inr (.ask a) :: callMoves c) q
  | .wait s a c m => ∃ p, p' = p.map relabel ++
      (.inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) : List (Move I.E (tsig I.F))) ∧
      I.Path P (.idle s₀) p (.idle s) ∧
      ∃ q, I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inl (.ask m)])) q
  | .dead => False
  | .stuck _ => False

theorem trun_concat {f : AFun I.E (Store Nat) I.F.Op (Ans I.F)} {Q : Pending I.E (Store Nat) I.F.Op}
    {x z : TSt I.E (Store Nat) I.F.Op} {p : List (Move I.E (tsig I.F))} {o : Move I.E (tsig I.F)}
    (h : TRun f Q x (p ++ [o]) z) : ∃ y, TRun f Q x p y ∧ TStep f Q y o z := by
  obtain ⟨y, hy, hz⟩ := h.of_append
  cases hz with
  | cons h hn => cases hn; exact ⟨y, hy, h⟩

theorem fwd {s₀ : Store Nat} {p' : List (Move I.E (tsig I.F))} {y : TSt I.E (Store Nat) I.F.Op}
    (h : TRun (instTriple I P).1 (satP (instTriple I P)) (.idle s₀) p' y) : FInv I P s₀ p' y := by
  induction p' using List.reverseRecOn generalizing y with
  | nil => cases h; exact ⟨[], rfl, .nil _⟩
  | append_singleton p' o ih =>
    obtain ⟨x, hx, hs⟩ := trun_concat h
    have hi := ih hx
    cases hs with
    | ask s a =>
      obtain ⟨p, rfl, hp⟩ := hi
      exact ⟨p, by simp [callMoves], hp, _, .cons (.call s a) (.nil _)⟩
    | call s a c m hm =>
      obtain ⟨p, rfl, hp, -⟩ := hi
      exact ⟨p, by simp, hp, satP_sound hm⟩
    | reply s a c m n =>
      obtain ⟨p, rfl, hp, q, hq⟩ := hi
      obtain ⟨q', hq'⟩ := path_reply (p := .inr (.ask a) :: callMoves c) hq n
      refine ⟨p, by rw [callMoves_concat]; simp, hp, q', ?_⟩
      rw [callMoves_concat]; exact hq'
    | ret s a c b s' hb =>
      obtain ⟨p, rfl, hp, -⟩ := hi
      rcases hb with ⟨v, s'', he, hr⟩ | ⟨he, -⟩
      · cases he
        refine ⟨p ++ .inr (.ask a) :: (callMoves c ++ [.inr (.ans a v)]), ?_, path_append hp hr⟩
        simp [relabel, map_relabel_callMoves]
      · cases he
    | trap s a c hb =>
      rcases hb with ⟨v, s'', he, -⟩ | ⟨he, -⟩ <;> cases he
    | deadAsk a => simp only [FInv] at hi

/-- The plays of the threaded instance are relabelled plays of the instance. -/
theorem fwd_mem {s₀ : Store Nat} {p' : List (Move I.E (tsig I.F))}
    (h : p' ∈ (instThread I P s₀).toStrategy) :
    ∃ p, p ∈ I.strategy P s₀ ∧ p.map relabel = p' := by
  obtain ⟨y, hy⟩ := StratThread.mem_threadT.1 h
  have hi := fwd hy
  simp only [ScalarInstance.mem_strategy_iff]
  rcases y with s | ⟨s, a, c⟩ | ⟨s, a, c, m⟩ | _ | a
  · obtain ⟨p, rfl, hp⟩ := hi
    exact ⟨p, ⟨_, hp⟩, rfl⟩
  · obtain ⟨p, rfl, hp, _, hq⟩ := hi
    exact ⟨_, ⟨_, path_append hp hq⟩, by simp [relabel, map_relabel_callMoves]⟩
  · obtain ⟨p, rfl, hp, _, hq⟩ := hi
    exact ⟨_, ⟨_, path_append hp hq⟩, by simp [relabel, map_relabel_callMoves]⟩
  · simp only [FInv] at hi
  · simp only [FInv] at hi

/-! ## From instance runs to threading runs -/

/-- The invariant of the backward simulation, on the hidden state of the instance. -/
def BInv (I : ScalarInstance) : I.HState → TSt I.E (Store Nat) I.F.Op → Prop
  | .idle s, y => y = .idle s
  | .running f s' t, y => ∃ s c, y = .run s f c ∧
      I.Path P (.idle s) (.inr (.ask f) :: callMoves c) (.running f s' t)
  | .waiting f s' t e, y => ∃ s c, y = .wait s f c e ∧
      I.Path P (.idle s) (.inr (.ask f) :: (callMoves c ++ [.inl (.ask e)])) (.waiting f s' t e)

theorem bwd {s₀ : Store Nat} {p : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.idle s₀) p q) :
    ∃ y, TRun (instTriple I P).1 (satP (instTriple I P)) (.idle s₀) (p.map relabel) y ∧
      BInv (P := P) I q y := by
  induction p using List.reverseRecOn generalizing q with
  | nil => cases h; exact ⟨_, .nil _, rfl⟩
  | append_singleton p o ih =>
    obtain ⟨x, hx, ht⟩ := path_concat h
    obtain ⟨y, hy, hi⟩ := ih hx
    rw [List.map_append]
    cases ht with
    | call s f =>
      cases hi
      exact ⟨_, hy.append (.cons (.ask s f) (.nil _)), s, [], rfl, .cons (.call s f) (.nil _)⟩
    | @ucall f s s' t t' h' args e run callout op =>
      obtain ⟨s₁, c, rfl, hr⟩ := hi
      have hp := path_append hr (path_single (.ucall (I := I) run callout op))
      exact ⟨_, hy.append (.cons (.call s₁ f c e (Or.inl ⟨_, hp⟩)) (.nil _)), s₁, c, rfl, hp⟩
    | @uret f s t e v =>
      obtain ⟨s₁, c, rfl, hw⟩ := hi
      have hp := path_append hw (path_single (.uret (I := I) (P := P) v))
      refine ⟨_, hy.append (.cons (.reply s₁ f c e v) (.nil _)), s₁, c ++ [⟨e, v⟩], rfl, ?_⟩
      rw [callMoves_concat]; simpa using hp
    | @oret f s s' t t' r v run final answer =>
      obtain ⟨s₁, c, rfl, hr⟩ := hi
      have hp := path_append hr (path_single (.oret (I := I) run final answer))
      have hmem : (c, End.ret (⟨f, v⟩ : Ans I.F) s') ∈ (instTriple I P).1 s₁ f :=
        Or.inl ⟨v, s', rfl, hp⟩
      exact ⟨_, hy.append (.cons (.ret s₁ f c _ s' hmem) (.nil _)), rfl⟩

/-! ## The main theorems -/

theorem mem_instThread {s₀ : Store Nat} {p' : List (Move I.E (tsig I.F))} :
    p' ∈ (instThread I P s₀).toStrategy ↔ ∃ p ∈ I.strategy P s₀, p.map relabel = p' := by
  refine ⟨fwd_mem, ?_⟩
  rintro ⟨p, hp, rfl⟩
  obtain ⟨q, hq⟩ := ScalarInstance.mem_strategy_iff.1 hp
  obtain ⟨y, hy, -⟩ := bwd hq
  exact StratThread.mem_threadT.2 ⟨y, hy⟩

theorem map_relabel_mem {s₀ : Store Nat} {p : List (Move I.E I.F)} :
    p.map relabel ∈ (instThread I P s₀).toStrategy ↔ p ∈ I.strategy P s₀ := by
  rw [mem_instThread]
  exact ⟨fun ⟨p₀, hp₀, he⟩ => List.map_injective_iff.2 relabel_injective he ▸ hp₀,
    fun hp => ⟨p, hp, rfl⟩⟩

theorem pull_instThread (s₀ : Store Nat) : pull (instThread I P s₀).toStrategy = I.strategy P s₀ :=
  le_antisymm (Strategy.generate_le fun _ hp _ => map_relabel_mem.1 hp) (by
    intro p hp
    exact Strategy.subset_generate (map_relabel_mem.2 hp) ((I.strategy P s₀).legal hp))

/-! ## Reachable stores -/

/-- The reachability invariant of a threading run. -/
def RInv (t : ObsTriple I.E (Store Nat) I.F.Op (Ans I.F)) (s₀ : Store Nat) :
    TSt I.E (Store Nat) I.F.Op → Prop
  | .idle s => StratThread.Reach t s₀ s
  | .run s _ _ => StratThread.Reach t s₀ s
  | .wait s _ _ _ => StratThread.Reach t s₀ s
  | .dead => True
  | .stuck _ => True

theorem trun_reach {t : ObsTriple I.E (Store Nat) I.F.Op (Ans I.F)} {s₀ : Store Nat}
    {x y : TSt I.E (Store Nat) I.F.Op} {p : List (Move I.E (tsig I.F))}
    (h : TRun t.1 (satP t) x p y) (hx : RInv t s₀ x) : RInv t s₀ y := by
  induction h with
  | nil => exact hx
  | cons hs _ ih =>
    apply ih
    cases hs with
    | ask => exact hx
    | call => exact hx
    | reply => exact hx
    | ret _ _ _ _ _ hb => exact StratThread.Reach.tail hx hb
    | trap => trivial
    | deadAsk => trivial

theorem reach_iff_reachableStore {s₀ s : Store Nat} :
    StratThread.Reach (instTriple I P) s₀ s ↔ I.ReachableStore P s₀ s := by
  constructor
  · intro h
    induction h with
    | refl s => exact ⟨[], ScalarInstance.Path.nil _⟩
    | step hb _ ih =>
      obtain ⟨c, hc⟩ := ih
      rcases hb with ⟨v, s'', he, hr⟩ | ⟨he, -⟩
      · cases he; exact ⟨_, path_append hr hc⟩
      · cases he
  · rintro ⟨c, hc⟩
    obtain ⟨y, hy, rfl⟩ := bwd hc
    exact trun_reach hy (StratThread.Reach.refl s₀)

end Silmaril.Proofs.Wasm.Abstract.InstStrat
