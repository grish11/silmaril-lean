module

public import Silmaril.Games.Abstract.StratLegal.Defs
public import Silmaril.Games.Abstract.StratObs.Thms

/-!
# Legal call/answer interfaces for the canonical play object (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratLegal

universe u

variable {E : Sig.{u}} {S A B : Type u} {L : (m : E.Op) → E.Ar m → Prop}
  {t : ObsTriple E S A B}

theorem callPre_map {c : List (Call (legalSig E L))} {m : E.Op} {d : List (Call (legalSig E L))}
    (h : CallPre c m d) : CallPre (c.map liftCall) m (d.map liftCall) := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨n.1, c'.map liftCall, by simp [liftCall]⟩

theorem streamTake_map (ω : ℕ → Call (legalSig E L)) (k : ℕ) :
    streamTake (fun n => liftCall (ω n)) k = (streamTake ω k).map liftCall := by
  simp [streamTake, List.map_ofFn, Function.comp_def]

theorem satP_restrict_sub {s : S} {a : A} {x : List (Call (legalSig E L)) × E.Op}
    (h : x ∈ satP (restrict L t) s a) : (x.1.map liftCall, x.2) ∈ satP t s a := by
  rcases h with h | ⟨d, m', hd, hp⟩ | ⟨d, e, hd, hp⟩ | ⟨ω, hω, k, hk, hm⟩
  · exact .inl h
  · exact .inr (.inl ⟨_, m', hd, callPre_map hp⟩)
  · exact .inr (.inr (.inl ⟨_, e, hd, callPre_map hp⟩))
  · refine .inr (.inr (.inr ⟨_, hω, k, ?_, hm⟩))
    rw [streamTake_map, hk]

theorem mem_satP_restrict (ht : Admissible t) {s : S} {a : A}
    {x : List (Call (legalSig E L)) × E.Op} :
    x ∈ satP (restrict L t) s a ↔ (x.1.map liftCall, x.2) ∈ t.2.1 s a := by
  refine ⟨fun h => ?_, fun h => .inl h⟩
  have := satP_restrict_sub h
  rwa [(saturated_iff.1 ht)] at this

theorem restrict_admissible (ht : Admissible t) : Admissible (restrict L t) := by
  refine saturated_iff.2 (funext fun s => funext fun a => Set.ext fun x => ?_)
  exact mem_satP_restrict ht

theorem astep_lift {x y : St (legalSig E L) S A} {o : Move (legalSig E L) (funSig S A B)}
    (h : AStep (restrict L t).1 (satP (restrict L t)) x o y) :
    AStep t.1 (satP t) (liftSt x) (liftMove o) (liftSt y) := by
  cases h with
  | ask q => exact .ask q
  | call q c m h => exact .call q (c.map liftCall) m (satP_restrict_sub (x := (c, m)) h)
  | reply q c m n =>
    show AStep _ _ (.wait q (c.map liftCall) m) (.inl (.ans m n.1))
      (.run q ((c ++ ([⟨m, n⟩] : List (Call (legalSig E L)))).map liftCall))
    rw [List.map_append]
    exact AStep.reply (f := t.1) (P := satP t) q (c.map liftCall) m n.1
  | ret q c r h => exact .ret q _ r h

theorem astep_unlift (ht : Admissible t) {x : St (legalSig E L) S A}
    {o : Move (legalSig E L) (funSig S A B)} {y' : St E S A}
    (h : AStep t.1 (satP t) (liftSt x) (liftMove o) y') :
    ∃ y, AStep (restrict L t).1 (satP (restrict L t)) x o y ∧ y' = liftSt y := by
  cases x with
  | idle =>
    simp only [liftSt] at h
    rcases o with (⟨m'⟩ | ⟨m', n'⟩) | (⟨q'⟩ | ⟨q', r'⟩) <;> simp only [liftMove, liftEv] at h <;>
      cases h
    exact ⟨_, .ask _, rfl⟩
  | run q c =>
    simp only [liftSt] at h
    rcases o with (⟨m'⟩ | ⟨m', n'⟩) | (⟨q'⟩ | ⟨q', r'⟩) <;> simp only [liftMove, liftEv] at h
    · cases h with
      | call _ _ _ hp =>
        exact ⟨_, .call _ _ _ ((mem_satP_restrict ht).2 ((saturated_iff.1 ht) ▸ hp)), rfl⟩
    · cases h
    · cases h
    · cases h with
      | ret _ _ _ hr => exact ⟨.idle, .ret _ _ _ hr, rfl⟩
  | wait q c m =>
    simp only [liftSt] at h
    rcases o with (⟨m'⟩ | ⟨m', n'⟩) | (⟨q'⟩ | ⟨q', r'⟩) <;> simp only [liftMove, liftEv] at h
    · cases h
    · cases h
      exact ⟨_, .reply _ _ _ _, by simp [liftSt, liftCall]⟩
    · cases h
    · cases h

theorem arun_lift {x y : St (legalSig E L) S A} {s : List (Move (legalSig E L) (funSig S A B))}
    (h : ARun (restrict L t).1 (satP (restrict L t)) x s y) :
    ARun t.1 (satP t) (liftSt x) (s.map liftMove) (liftSt y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (astep_lift hs) ih

theorem arun_unlift (ht : Admissible t) {x : St (legalSig E L) S A}
    {s : List (Move (legalSig E L) (funSig S A B))} {y' : St E S A}
    (h : ARun t.1 (satP t) (liftSt x) (s.map liftMove) y') :
    ∃ y, ARun (restrict L t).1 (satP (restrict L t)) x s y ∧ y' = liftSt y := by
  induction s generalizing x with
  | nil => cases h; exact ⟨x, .nil _, rfl⟩
  | cons o s ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨z, hz, rfl⟩ := astep_unlift ht hs
      obtain ⟨y, hy, rfl⟩ := ih hr
      exact ⟨y, .cons hz hy, rfl⟩

theorem mem_toDStratL (ht : Admissible t) {s : List (Move (legalSig E L) (funSig S A B))} :
    s ∈ (toDStratL L t).toStrategy ↔ s.map liftMove ∈ (toDStrat t).toStrategy := by
  rw [toDStratL, mem_toDStrat, mem_toDStrat]
  constructor
  · rintro ⟨y, h⟩
    exact ⟨_, arun_lift (x := .idle) h⟩
  · rintro ⟨y', h⟩
    obtain ⟨y, hy, -⟩ := arun_unlift (x := .idle) ht h
    exact ⟨y, hy⟩

end Silmaril.Proofs.Games.Abstract.StratLegal
