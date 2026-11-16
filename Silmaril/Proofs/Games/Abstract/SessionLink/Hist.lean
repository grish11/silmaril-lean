module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Plays
import Mathlib.Data.List.Basic

/-!
# Linking sessions: the forward simulation with the server's history (proofs)

`JH t u s₀ w x y z` refines `J` by the server's play `w` so far: it is the moves of the server's
completed session rounds `R` (before the current linked round) and `rs` (serving the current
linked round), then the server's partial round. `fwdH` is the forward simulation `fwd` keeping
track of it. The infinite parts of the forward direction compare `w` with a coherent infinite
play of the server, to pin the stores of the linked round.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-- Related states of the three automata, with the server's play so far. -/
inductive JH (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) (s₀ : S) :
    List (Move E (sig1 A B)) → TSt E S A → TSt (sig1 A B) S' A' → TSt E (S × S') A' → Prop
  | idle (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) (s' : S') :
      Rounds t s₀ R s → JH t u s₀ (sroundsMoves R) (.idle s) (.idle s') (.idle (s, s'))
  | run (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (σ : S × S') (a' : A')
      (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) :
      Rounds t s₀ R σ.1 → Rounds t σ.1 rs s →
      JH t u s₀ (sroundsMoves (R ++ rs)) (.idle s) (.run σ.2 a' (served rs))
        (.run σ a' (servedLog rs))
  | call (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (σ : S × S') (a' : A')
      (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) (a : A) (c : List (Call E)) :
      Rounds t s₀ R σ.1 → Rounds t σ.1 rs s → (served rs, a) ∈ satP u σ.2 a' →
      JH t u s₀ (sroundsMoves (R ++ rs) ++ .inr (.ask a) :: callMoves c) (.run s a c)
        (.wait σ.2 a' (served rs) a) (.run σ a' (servedLog rs ++ c))
  | wait (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (σ : S × S') (a' : A')
      (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) (a : A) (c : List (Call E))
      (m : E.Op) : Rounds t s₀ R σ.1 → Rounds t σ.1 rs s → (served rs, a) ∈ satP u σ.2 a' →
      JH t u s₀ (sroundsMoves (R ++ rs) ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]))
        (.wait s a c m) (.wait σ.2 a' (served rs) a) (.wait σ a' (servedLog rs ++ c) m)
  | dead (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) :
      Rounds t s₀ R s → JH t u s₀ (sroundsMoves R) (.idle s) .dead .dead
  | stuck (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) (a' : A') :
      Rounds t s₀ R s → JH t u s₀ (sroundsMoves R) (.idle s) (.stuck a') (.stuck a')

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})} {s₀ : S}

theorem JH.cast {w w' : List (Move E (sig1 A B))} {x : TSt E S A} {y : TSt (sig1 A B) S' A'}
    {z : TSt E (S × S') A'} (h : JH t u s₀ w x y z) (e : w = w') : JH t u s₀ w' x y z :=
  e ▸ h

/-- **Forward, with the server's history.** -/
theorem fwdH (hnt : NoPlainTrap t) {sv : List (Move E (sig1 A B))}
    {cv : List (Move (sig1 A B) (sig1 A' B'))} {p : List (Move E (sig1 A' B'))}
    (hz : Zip sv cv p) :
    ∀ {w x x' y y' z}, JH t u s₀ w x y z → SRun t x sv x' → SRun u y cv y' →
      ∃ z', SRun (linkS t u) z p z' ∧ JH t u s₀ (w ++ sv) x' y' z' := by
  induction hz with
  | nil =>
    intro w x x' y y' z hJ hv hc
    cases hv; cases hc
    exact ⟨z, .nil _, hJ.cast (by simp)⟩
  | left e _ ih =>
    intro w x x' y y' z hJ hv hc
    cases hv with
    | cons hst hr =>
      cases hst with
      | call s a c m hP =>
        cases hJ with
        | call R σ a' rs _ _ _ hR₀ hR hu =>
          obtain ⟨z', hz', hJ'⟩ := ih (JH.wait R σ a' rs s a c m hR₀ hR hu) hr hc
          exact ⟨z', .cons (.call σ a' _ m (.inl ⟨rs, s, a, c, hR, hu, hP, rfl⟩)) hz',
            hJ'.cast (by simp)⟩
      | reply s a c m n =>
        cases hJ with
        | wait R σ a' rs _ _ _ _ hR₀ hR hu =>
          obtain ⟨z', hz', hJ'⟩ := ih (JH.call R σ a' rs s a (c ++ [⟨m, n⟩]) hR₀ hR hu) hr hc
          have hs := SStep.reply (t := linkS t u) σ a' (servedLog rs ++ c) m n
          rw [List.append_assoc] at hs
          exact ⟨z', .cons hs hz', hJ'.cast (by simp)⟩
  | right g _ ih =>
    intro w x x' y y' z hJ hv hc
    cases hc with
    | cons hst hr =>
      cases hst with
      | ask s' a' =>
        cases hJ with
        | idle R s _ hR =>
          obtain ⟨z', hz', hJ'⟩ :=
            ih ((JH.run (u := u) R (s, s') a' [] s hR (.nil _)).cast (w' := sroundsMoves R) (by simp)) hv hr
          exact ⟨z', .cons (.ask (s, s') a') hz', hJ'⟩
      | ret _ _ _ b s'' hb =>
        cases hJ with
        | run R σ a' rs s hR₀ hR =>
          obtain ⟨z', hz', hJ'⟩ := ih (JH.idle (u := u) (R ++ rs) s s'' (rounds_append hR₀ hR))
            hv hr
          exact ⟨z', .cons (.ret σ _ _ b (s, s'') (.inl ⟨rs, s, .ret b s'', hR, hb, rfl⟩)) hz',
            hJ'⟩
      | trap _ _ _ hb =>
        cases hJ with
        | run R σ a' rs s hR₀ hR =>
          obtain ⟨z', hz', hJ'⟩ := ih (JH.dead (u := u) (R ++ rs) s (rounds_append hR₀ hR)) hv hr
          exact ⟨z', .cons (.trap σ _ _ (.inl ⟨rs, s, .trap, hR, hb, rfl⟩)) hz', hJ'⟩
      | deadAsk a' =>
        cases hJ with
        | dead R s hR =>
          obtain ⟨z', hz', hJ'⟩ := ih (JH.stuck (u := u) R s a' hR) hv hr
          exact ⟨z', .cons (.deadAsk a') hz', hJ'⟩
  | sync b _ ih =>
    intro w x x' y y' z hJ hv hc
    cases hv with
    | cons hst hr =>
      cases hc with
      | cons hct hcr =>
        cases hst with
        | ask s a =>
          cases hct with
          | call _ a' _ _ hP =>
            cases hJ with
            | run R σ _ rs _ hR₀ hR =>
              have hJ' := JH.call R σ a' rs s a [] hR₀ hR hP
              rw [List.append_nil] at hJ'
              obtain ⟨z', hz', hJ''⟩ := ih hJ' hr hcr
              exact ⟨z', hz', hJ''.cast (by simp)⟩
        | ret s a c x s₂ hb =>
          cases hct with
          | reply _ a' =>
            cases hJ with
            | call R σ _ rs _ _ _ hR₀ hR hu =>
              have hJ' := JH.run (u := u) R σ a' (rs ++ [(a, c, x)]) s₂ hR₀ (rounds_snoc hR hb)
              simp only [served_append, served_cons, served_nil, servedLog_append,
                servedLog_cons, servedLog_nil, List.append_nil] at hJ'
              obtain ⟨z', hz', hJ''⟩ := ih hJ' hr hcr
              exact ⟨z', hz', hJ''.cast (by simp [sroundMoves])⟩
        | trap s a c hb => exact absurd hb (hnt s a c)
        | deadAsk => cases hJ

end Silmaril.Proofs.Games.Abstract.SessionLink
