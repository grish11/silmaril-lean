module

public import Silmaril.Games.Abstract.SessionExt.Defs
public import Silmaril.Games.Abstract.SessionRoute.Thms
public import Silmaril.Games.Abstract.SessionPairMap.Thms
public import Silmaril.Games.AnsMap.Thms
public import Silmaril.Games.DivComp.Thms

/-!
# Extending an environment by a session node, on session interfaces (proofs)

* `relabelPair_eq_mapAns`: `StratSession.relabelPair` relabels answers along `pairAnswer`.
* `mapS_callS`: mapping a one-call triple is a one-call triple.
* `ofHandler_routeH`: the routing handler is the answer relabelling of the pairing followed by
  a one-call handler on the paired session interface, as linked one-call sessions.
* `pair_comp_routeH`: two sessions side by side below the routing handler are the session of
  `routeS`: relabel the pairing (`DStrategy.comp_ansH`), which is the paired session
  (`StratSession.threadS_pairS`), then route it (`SessionRoute.threadS_comp_callH`).
* `extS_threadS`: with copycat as the session of `idS`, the environment's session serves the
  routed session (`SessionLink.comp_threadS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionExt

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionRoute Silmaril.Games.Abstract.SessionExt

universe u

section Pair

variable {E : Sig.{u}} {A₁ A₂ B₁ B₂ : Type u}

theorem pairMove_eq_ansMove :
    (pairMove : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂) → _) = ansMove pairAnswer := by
  funext o
  rcases o with e | (a | ⟨a | a, x⟩) <;> rfl

/-- **`relabelPair` relabels answers along `pairAnswer`.** -/
theorem relabelPair_eq_mapAns (σ : DStrategy E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)) :
    relabelPair σ = σ.mapAns pairAnswer := by
  refine DStrategy.ext (Strategy.ext fun p => ?_) ?_ ?_
  · show (∃ q ∈ σ.toStrategy.plays, q.map pairMove = p) ↔
      ∃ q ∈ σ.toStrategy.plays, q.map (ansMove pairAnswer) = p
    rw [pairMove_eq_ansMove]
    exact Iff.rfl
  · show {p | ∃ q ∈ σ.div, q.map pairMove = p} = {p | ∃ q ∈ σ.div, q.map (ansMove pairAnswer) = p}
    rw [pairMove_eq_ansMove]
    rfl
  · show {K | ∃ J ∈ σ.inf, K = List.map pairMove '' J} =
      {K | ∃ J ∈ σ.inf, K = List.map (ansMove pairAnswer) '' J}
    rw [pairMove_eq_ansMove]
    rfl

theorem agree_map {S S' B B' : Type u} (k : End S B → End S' B') {c₁ c₂ : List (Call E)}
    {e₁ e₂ : End S B} (h : AFun.Agree c₁ e₁ c₂ e₂) : AFun.Agree c₁ (k e₁) c₂ (k e₂) := by
  induction c₁ generalizing c₂ with
  | nil =>
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact congrArg k h
    · exact h.elim
  | cons x c₁ ih =>
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact h.elim
    · obtain ⟨m₁, n₁⟩ := x
      exact ⟨h.1, fun hn => ih (h.2 hn)⟩

variable {S₁ S₂ : Type u}

/-- **Pairing keeps deterministic returns.** -/
theorem retDet_pairS {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
    {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})} (h₁ : RetDet t₁) (h₂ : RetDet t₂) :
    RetDet (pairS t₁ t₂) := by
  rintro σ (a | a) c c' b b' σ₁ σ₁' hc hc'
  · obtain ⟨e, he, hx⟩ := mem_pairS_inl.1 hc
    obtain ⟨e', he', hx'⟩ := mem_pairS_inl.1 hc'
    cases e with
    | trap => cases hx
    | div => cases hx
    | ret x s =>
      cases e' with
      | trap => cases hx'
      | div => cases hx'
      | ret x' s' =>
        dsimp only at hx hx' he he'
        rw [hx, hx']
        exact agree_map (pairEndL σ.2) (h₁ _ _ _ _ _ _ _ _ he he')
  · obtain ⟨e, he, hx⟩ := mem_pairS_inr.1 hc
    obtain ⟨e', he', hx'⟩ := mem_pairS_inr.1 hc'
    cases e with
    | trap => cases hx
    | div => cases hx
    | ret x s =>
      cases e' with
      | trap => cases hx'
      | div => cases hx'
      | ret x' s' =>
        dsimp only at hx hx' he he'
        rw [hx, hx']
        exact agree_map (pairEndR σ.1) (h₂ _ _ _ _ _ _ _ _ he he')

end Pair

/-- **Mapping a one-call triple is a one-call triple.** -/
theorem mapS_callS {E : Sig.{u}} {A A' B B' : Type u} (g : A → E.Op)
    (f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}) (g' : A' → A)
    (f' : A' → B ⊕ PUnit.{u + 1} → B' ⊕ PUnit.{u + 1}) :
    mapS g' f' (callS g f) = callS (fun a => g (g' a)) (fun a n => f' a (f (g' a) n)) := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  funext s a
  ext x
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, rfl⟩

variable {A A₁ A₂ B : Type u}

theorem foldS_pairAnswer (a : (sig1 A₁ B ⊕ₛ sig1 A₂ B).Op) (n : (sig1 A₁ B ⊕ₛ sig1 A₂ B).Ar a) :
    foldS (pairAnswer a n) = unsum a n := by
  rcases a with a | a <;> rcases n with n | n <;> rfl

/-- **The routing handler factors** through the paired session interface. -/
theorem ofHandler_routeH (r : A → A₁ ⊕ A₂) :
    DStrategy.ofHandler (routeH (B := B) r) =
      (DStrategy.ofHandler (ansH (pairAnswer (A₁ := A₁) (A₂ := A₂) (B₁ := B) (B₂ := B)))).comp
        (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS)) := by
  have h₂ : (fun (a : A) (n : (sig1 A₁ B ⊕ₛ sig1 A₂ B).Ar (r a)) => foldS (pairAnswer (r a) n)) =
      fun a => unsum (r a) := by
    funext a n
    exact foldS_pairAnswer (r a) n
  have h₃ : threadS (callS (E := sig1 A₁ B ⊕ₛ sig1 A₂ B) r fun a => unsum (r a)) PUnit.unit =
      threadS (mapS r (fun _ => foldS)
        (callS (E := sig1 A₁ B ⊕ₛ sig1 A₂ B) (fun a => a) pairAnswer)) PUnit.unit :=
    congrArg (fun t => threadS t PUnit.unit)
      ((mapS_callS (E := sig1 A₁ B ⊕ₛ sig1 A₂ B) (fun a => a) pairAnswer r (fun _ => foldS)).trans
        (congrArg (callS (E := sig1 A₁ B ⊕ₛ sig1 A₂ B) r) h₂)).symm
  calc DStrategy.ofHandler (routeH (B := B) r)
      = threadS (callS (E := sig1 A₁ B ⊕ₛ sig1 A₂ B) r fun a => unsum (r a)) PUnit.unit :=
        threadS_callS.symm
    _ = _ := h₃
    _ = (threadS (callS (E := sig1 A₁ B ⊕ₛ sig1 A₂ B) (fun a => a) pairAnswer) PUnit.unit).comp
          (DStrategy.ofHandler (callH r fun _ => foldS)) :=
        (threadS_comp_callH noPlainTrap_callS retDet_callS PUnit.unit).symm
    _ = _ := congrArg (fun x => DStrategy.comp x _) threadS_callS

variable {E : Sig.{u}} {S₁ S₂ : Type u} {t₁ : ObsTriple E S₁ A₁ (B ⊕ PUnit.{u + 1})}
  {t₂ : ObsTriple E S₂ A₂ (B ⊕ PUnit.{u + 1})}

/-- **Two sessions side by side below the routing handler are the routed session.** -/
theorem pair_comp_routeH (r : A → A₁ ⊕ A₂) (hn₁ : NoPlainTrap t₁) (hd₁ : RetDet t₁)
    (hn₂ : NoPlainTrap t₂) (hd₂ : RetDet t₂) (s₁ : S₁) (s₂ : S₂) :
    ((threadS t₁ s₁).pair (threadS t₂ s₂)).comp (DStrategy.ofHandler (routeH r)) =
      threadS (routeS r t₁ t₂) (s₁, s₂) := by
  calc ((threadS t₁ s₁).pair (threadS t₂ s₂)).comp (DStrategy.ofHandler (routeH r))
      = ((threadS t₁ s₁).pair (threadS t₂ s₂)).comp
          ((DStrategy.ofHandler (ansH pairAnswer)).comp
            (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS))) :=
        congrArg _ (ofHandler_routeH r)
    _ = (((threadS t₁ s₁).pair (threadS t₂ s₂)).comp (DStrategy.ofHandler (ansH pairAnswer))).comp
          (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS)) :=
        (DStrategy.comp_assoc _ _ _).symm
    _ = (((threadS t₁ s₁).pair (threadS t₂ s₂)).mapAns pairAnswer).comp
          (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS)) :=
        congrArg (fun x => DStrategy.comp x _) (DStrategy.comp_ansH _ _)
    _ = (relabelPair ((threadS t₁ s₁).pair (threadS t₂ s₂))).comp
          (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS)) :=
        congrArg (fun x => DStrategy.comp x _) (relabelPair_eq_mapAns _).symm
    _ = (threadS (pairS t₁ t₂) (s₁, s₂)).comp
          (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS)) :=
        congrArg (fun x => DStrategy.comp x _) (threadS_pairS hn₁ hn₂ s₁ s₂).symm
    _ = threadS (routeS r t₁ t₂) (s₁, s₂) :=
        threadS_comp_callH (noPlainTrap_pairS hn₁ hn₂) (retDet_pairS hd₁ hd₂) (s₁, s₂)

theorem noPlainTrap_routeS (r : A → A₁ ⊕ A₂) (hn₁ : NoPlainTrap t₁) (hn₂ : NoPlainTrap t₂) :
    NoPlainTrap (routeS r t₁ t₂) :=
  noPlainTrap_mapS (noPlainTrap_pairS hn₁ hn₂)

theorem retDet_routeS (r : A → A₁ ⊕ A₂) (hd₁ : RetDet t₁) (hd₂ : RetDet t₂) :
    RetDet (routeS r t₁ t₂) :=
  retDet_mapS (retDet_pairS hd₁ hd₂)

/-- **Extending a session environment by a session node is a linked session.** -/
theorem extS_threadS {X : Sig.{u}} {S S' : Type u} {u : ObsTriple X S' A (B ⊕ PUnit.{u + 1})}
    {t : ObsTriple (sig1 A B) S A₂ (B ⊕ PUnit.{u + 1})} (r : A → A ⊕ A₂) (hnu : NoPlainTrap u)
    (hdu : RetDet u) (hnt : NoPlainTrap t) (hdt : RetDet t) (s' : S') (s : S) :
    extS r (threadS u s') (threadS t s) =
      threadS (linkS u (routeS r idS t)) (s', (PUnit.unit, s)) := by
  rw [extS, ← threadS_idS, pair_comp_routeH r noPlainTrap_idS retDet_idS hnt hdt,
    comp_threadS hnu (storeDet_of_retDet hdu)
      (storeDet_of_retDet (retDet_linkS hdu (retDet_routeS r retDet_idS hdt)))]

end Silmaril.Proofs.Games.Abstract.SessionExt
