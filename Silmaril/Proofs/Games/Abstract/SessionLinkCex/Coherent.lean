module

public import Silmaril.Proofs.Games.Abstract.SessionLinkCex.Basic
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DivComp.Defs

/-!
# Linking counterexamples: a non-coherent server

The countdown server answers any finite number of calls from `none`, so the chattering client,
asked once, has an infinite interaction with it: the composite diverges after the question. No
infinite service by the countdown is coherent (`not_infServe`), so the linked triple does not
diverge there.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionLinkCex

variable {E : Sig.{0}}

theorem noPlainTrap_cdServer : NoPlainTrap (cdServer (E := E)) := by
  rintro _ _ _ ⟨_, _, h⟩
  simp at h

theorem not_storeDet_cdServer : ¬ StoreDet (cdServer (E := E)) := by
  intro h
  have := h none () [] (.inl ()) (some 0) (some 1) ⟨0, .inl rfl, rfl⟩ ⟨1, .inl rfl, rfl⟩
  simp at this

theorem storeDet_linkS_cd : StoreDet (linkS (cdServer (E := E)) chatClient) := by
  rintro _ _ _ _ _ _ (⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, _, _, _, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩)
  · simp [chatClient] at he
  · simp at hx
  · simp at hx

/-- **No infinite service by the countdown is coherent.** -/
theorem not_infServe {ω : ℕ → Call (sig1 Unit Unit)} {l : ℕ → List (Call E)}
    {st : ℕ → Option ℕ} : ¬ InfServe (cdServer (E := E)) none ω l st := by
  intro h
  obtain ⟨n₀, -, h₀⟩ := h.step 0
  simp only [Prod.mk.injEq, End.ret.injEq] at h₀
  have key : ∀ j, ∃ m, st (j + 1) = some m ∧ m + j = n₀ := by
    intro j
    induction j with
    | zero => exact ⟨n₀, h₀.2.2, rfl⟩
    | succ j ih =>
      obtain ⟨m, hm, hmj⟩ := ih
      obtain ⟨n, hn, hr⟩ := h.step (j + 1)
      rw [hm] at hn
      simp only [Prod.mk.injEq, End.ret.injEq] at hr
      rcases hn with hn | hn
      · cases hn
      · cases hn
        exact ⟨n, hr.2.2, by omega⟩
  obtain ⟨m, -, hm⟩ := key (n₀ + 1)
  omega

/-! ## The chattering interaction -/

theorem cd_down (m : ℕ) :
    Rounds (cdServer (E := E)) (some m) (List.replicate m ((), [], .inl ())) (some 0) := by
  induction m with
  | zero => exact .nil _
  | succ m ih => rw [List.replicate_succ]; exact .cons ⟨m, .inr rfl, rfl⟩ ih

theorem cd_none (n : ℕ) :
    ∃ s, Rounds (cdServer (E := E)) none (streamTake (fun _ => ((), [], .inl ())) n) s := by
  rw [streamTake_const]
  cases n with
  | zero => exact ⟨_, .nil _⟩
  | succ n => rw [List.replicate_succ]; exact ⟨_, .cons ⟨n, .inl rfl, rfl⟩ (cd_down n)⟩

theorem length_callMoves {F : Sig.{0}} (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    show (callMoves c : List (Move E F)).length + 2 = _
    rw [ih, List.length_cons]; omega

theorem zip_chat (n : ℕ) :
    Zip (sroundsMoves (List.replicate n ((), ([] : List (Call E)), (.inl () : Unit ⊕ Unit))))
      (callMoves (List.replicate n chatCall) : List (Move (sig1 Unit Unit) (sig1 Unit Unit)))
      [] := by
  induction n with
  | zero => exact .nil
  | succ n ih => rw [List.replicate_succ, List.replicate_succ]; exact .sync _ (.sync _ ih)

/-- The infinite interaction of the countdown server with the chattering client. -/
def chatInter :
    DStrategy.InfInteraction (threadS (cdServer (E := E)) none) (threadS chatClient ()) where
  s n := sroundsMoves (streamTake (fun _ => ((), [], .inl ())) n)
  t n := .inr (.ask ()) :: callMoves (streamTake (fun _ => chatCall) n)
  p _ := [.inr (.ask ())]
  zip n := by
    rw [streamTake_const, streamTake_const]
    exact .right _ (zip_chat n)
  mem_s n := mem_srounds.2 (.inl (cd_none n))
  mem_t n := by
    have h := (StratSession.mem_pending (t := chatClient) (s₀ := ()) (rs := []) (a := ())
      (c := streamTake (fun _ => chatCall) n) (m := ())).2
      ⟨(), .nil _, .inr (.inr (.inr ⟨_, rfl, n, rfl, rfl⟩))⟩
    exact (threadS chatClient ()).toStrategy.of_prefix h ⟨_, rfl⟩
  mono_s n := by
    simp only [streamTake_const, List.replicate_succ', sroundsMoves, List.flatMap_append]
    exact List.prefix_append _ _
  mono_t n := by
    simp only [streamTake_const, List.replicate_succ', callMoves, List.flatMap_append]
    exact (List.prefix_cons_inj _).2 (List.prefix_append _ _)
  mono_p _ := List.prefix_refl _
  unbounded k := ⟨k, by
    simp only [length_callMoves, List.length_cons, streamTake, List.length_ofFn]; omega⟩
  lim_s _ := mem_inf_iff.2 (.inr ⟨fun _ => (), fun _ => ([], .inl ()), rfl, cd_none⟩)
  lim_t _ := (StratSession.mem_inf (rs := [])).2 ⟨(), .nil _, rfl⟩

theorem div_comp_chat :
    [.inr (.ask ())] ∈ ((threadS (cdServer (E := E)) none).comp (threadS chatClient ())).div :=
  .inr ⟨chatInter, fun _ => rfl⟩

theorem not_div_linkS_chat :
    [.inr (.ask ())] ∉ (threadS (linkS (cdServer (E := E)) chatClient) (none, ())).div := by
  intro h
  obtain ⟨rs, σ, a, c, hr, hd, he⟩ := StratSession.mem_div_iff.1 h
  rcases rs with _ | ⟨r, rs⟩
  · rcases c with _ | ⟨x, c⟩
    · cases rounds_nil_iff.1 hr
      rcases hd with ⟨_, _, _, _, he, _⟩ | ⟨_, _, _, _, _, _, ⟨_, _, hx⟩, _⟩ |
        ⟨_, _, _, _, _, hinf, _, _⟩
      · simp [chatClient] at he
      · simp at hx
      · exact not_infServe hinf
    · simp [callMoves, sroundsMoves] at he
  · simp [sroundsMoves, sroundMoves] at he

end Silmaril.Proofs.Games.Abstract.SessionLinkCex
