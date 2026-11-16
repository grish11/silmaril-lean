module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkIR
public import Silmaril.Games.Handler.Thms

/-!
# Plays of linked components with host imports: game lemmas

Rounds with lower calls (`CRound`, `cplay`) through the layers that `Linked2` does not need:

* **mixed pairings** (`cplay_pair_mixed`): rounds of both components of `σ₁.pair σ₂`,
  interleaved, are a play of the pairing when the left rounds are a play of `σ₁` and the right
  rounds a play of `σ₂` (`halves_cplay_mixed`);
* **copycat** (`cplay_id_calls`): copycat answers each round by the same call below;
* **serving with lower calls** (`cplay_comp_serveC`): when the strategy below answers the lower
  calls of the strategy on top by rounds that make lower calls of their own, the composite
  plays the rounds with those calls visible (`cplay_comp_serve` is the case without calls);
* rounds without lower calls are `twos` (`cplay_nocalls`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference

variable {E F G : Sig.{0}}

theorem callMoves_appendH {E F : Sig.{0}} :
    ∀ (a b : List (Round E)), callMoves (F := F) (a ++ b) = callMoves a ++ callMoves b
  | [], _ => rfl
  | ⟨_, _⟩ :: a, b => by
    rw [List.cons_append]
    simp only [callMoves, callMoves_appendH a b, List.cons_append]

/-! ## Mixed rounds of a pairing -/

/-- A round of one of the two components of a pairing, as a round of the pairing. -/
def CRound.lift {F₁ F₂ : Sig.{0}} : CRound E F₁ ⊕ CRound E F₂ → CRound E (F₁ ⊕ₛ F₂)
  | .inl r => ⟨.inl r.q, r.cs, r.a⟩
  | .inr r => ⟨.inr r.q, r.cs, r.a⟩

/-- The rounds of the left component. -/
def lefts {F₁ F₂ : Sig.{0}} : List (CRound E F₁ ⊕ CRound E F₂) → List (CRound E F₁)
  | [] => []
  | .inl r :: l => r :: lefts l
  | .inr _ :: l => lefts l

/-- The rounds of the right component. -/
def rights {F₁ F₂ : Sig.{0}} : List (CRound E F₁ ⊕ CRound E F₂) → List (CRound E F₂)
  | [] => []
  | .inl _ :: l => rights l
  | .inr r :: l => r :: rights l

theorem halves_calls_false {F₁ F₂ : Sig.{0}} :
    ∀ (cs : List (Round E)) (rest : List (Move E (F₁ ⊕ₛ F₂))),
      Split.halves false (callMoves cs ++ rest) =
        (callMoves cs ++ (Split.halves false rest).1, (Split.halves false rest).2)
  | [], _ => rfl
  | ⟨m, n⟩ :: cs, rest => by
    show Split.halves false (.inl (.ask m) :: .inl (.ans m n) :: (callMoves cs ++ rest)) = _
    simp only [Split.halves, halves_calls_false cs rest]
    rfl

theorem halves_cplay_mixed {F₁ F₂ : Sig.{0}} :
    ∀ (b : Bool) (l : List (CRound E F₁ ⊕ CRound E F₂)),
      Split.halves b (cplay (l.map CRound.lift)) = (cplay (lefts l), cplay (rights l))
  | _, [] => rfl
  | b, .inl ⟨q, cs, a⟩ :: l => by
    show Split.halves b (.inr (.ask (.inl q)) :: (callMoves cs ++
      (.inr (.ans (.inl q) a) :: cplay (l.map CRound.lift)))) = _
    simp only [Split.halves, halves_calls_false, halves_cplay_mixed false l]
    rfl
  | b, .inr ⟨q, cs, a⟩ :: l => by
    show Split.halves b (.inr (.ask (.inr q)) :: (callMoves cs ++
      (.inr (.ans (.inr q) a) :: cplay (l.map CRound.lift)))) = _
    simp only [Split.halves, halves_calls, halves_cplay_mixed true l]
    rfl

/-- **Rounds of both components of a pairing**, interleaved. -/
theorem cplay_pair_mixed {F₁ F₂ : Sig.{0}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (CRound E F₁ ⊕ CRound E F₂)} (h₁ : cplay (lefts l) ∈ σ₁)
    (h₂ : cplay (rights l) ∈ σ₂) : cplay (l.map CRound.lift) ∈ σ₁.pair σ₂ := by
  refine ⟨legal_cplay _, ?_, ?_⟩
  · rw [halves_cplay_mixed]
    exact h₁
  · rw [halves_cplay_mixed]
    exact h₂

/-! ## Copycat -/

theorem run_id :
    ∀ rs : List (Round E), (Handler.id E).toReduction.toLTS.Run .idle
      (cplay (rs.map fun r => (⟨r.1, [r], r.2⟩ : CRound E E))) .idle
  | [] => .nil _
  | ⟨q, a⟩ :: rs =>
    .vis (.ask q) (.vis (.call (show Handler.id E q = .call q Prog.pure from rfl))
      (.vis (Reduction.Step.resume (R := (Handler.id E).toReduction) q q Prog.pure a)
        (.vis (.ret (show (Prog.pure a : Prog E (E.Ar q)) = .pure a from rfl)) (run_id rs))))

/-- **Copycat answers each round by the same call below.** -/
theorem cplay_id_calls (rs : List (Round E)) :
    cplay (rs.map fun r => (⟨r.1, [r], r.2⟩ : CRound E E)) ∈ Strategy.id E := by
  rw [← Strategy.ofHandler_id]
  exact Strategy.mem_ofHandler.mpr ⟨_, run_id rs⟩

/-- Rounds without lower calls are `twos`. -/
theorem cplay_nocalls :
    ∀ rs : List (Round F), cplay (rs.map fun r => (⟨r.1, [], r.2⟩ : CRound E F)) = twos rs
  | [] => rfl
  | ⟨q, a⟩ :: rs => by
    show .inr (.ask q) :: (callMoves [] ++ (.inr (.ans q a) ::
      cplay (rs.map fun r => (⟨r.1, [], r.2⟩ : CRound E F)))) = _
    rw [cplay_nocalls rs]
    rfl

/-! ## Serving with lower calls -/

/-- A round of the strategy on top whose lower calls are answered by the rounds `subs` of the
strategy below, which may make lower calls of their own. -/
structure SRound (E F G : Sig.{0}) where
  q : G.Op
  subs : List (CRound E F)
  a : G.Ar q

/-- The round of the strategy on top. -/
def SRound.up (r : SRound E F G) : CRound F G :=
  ⟨r.q, r.subs.map fun x => (⟨x.q, x.a⟩ : Round F), r.a⟩

/-- The round of the composite: the lower calls of the rounds below are visible. -/
def SRound.vis (r : SRound E F G) : CRound E G := ⟨r.q, r.subs.flatMap (·.cs), r.a⟩

theorem zip_subs {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ subs : List (CRound E F),
      Zip (cplay subs ++ s) (callMoves (subs.map fun x => (⟨x.q, x.a⟩ : Round F)) ++ t)
        (callMoves (subs.flatMap (·.cs)) ++ p)
  | [] => h
  | x :: subs => by
    have ih := zip_subs h subs
    rw [List.flatMap_cons, callMoves_appendH, List.append_assoc]
    show Zip (.inr (.ask x.q) :: (callMoves x.cs ++ (.inr (.ans x.q x.a) :: cplay subs)) ++ s)
      (.inl (.ask x.q) :: .inl (.ans x.q x.a) ::
        (callMoves (subs.map fun x => (⟨x.q, x.a⟩ : Round F)) ++ t)) _
    rw [List.cons_append, List.append_assoc, List.cons_append]
    exact .sync _ (zip_calls_left (.sync _ ih) x.cs)

theorem zip_serveC : ∀ L : List (SRound E F G),
    Zip (cplay (L.flatMap (·.subs))) (cplay (L.map SRound.up)) (cplay (L.map SRound.vis))
  | [] => .nil
  | r :: L => by
    rw [List.flatMap_cons, cplay_append]
    exact .right _ (zip_subs (.right _ (zip_serveC L)) r.subs)

/-- **A strategy below serving the lower calls by rounds with lower calls**: the composite
plays the rounds on top with the lower calls of the rounds below visible. -/
theorem cplay_comp_serveC {σ : Strategy E F} {τ : Strategy F G} {L : List (SRound E F G)}
    (hσ : cplay (L.flatMap (·.subs)) ∈ σ) (hτ : cplay (L.map SRound.up) ∈ τ) :
    cplay (L.map SRound.vis) ∈ σ.comp τ :=
  ⟨_, hσ, _, hτ, zip_serveC L⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
