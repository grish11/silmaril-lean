module

public import Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.Basic
public import Silmaril.Games.Abstract.SessionCat.Defs

/-!
# Linking sessions: literal unit laws (proofs)

The identity session `idS` as a client forwards each question once and returns the answer: a
linked round is one round of the server, a returning or continuing-trap round or a divergence; the
server's plain traps are dropped. As a server, `idS` answers every call at once with that very
call: a linked round is a round of the client, whose import log is its log of calls.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkAssoc

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionLinkAssoc Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S A B A' B' : Type u}

/-- The call prefixes of the identity session: the forwarded question, before any call. -/
theorem satP_idS {p : PUnit.{u + 1}} {a : A} {x : List (Call (sig1 A B)) × A} :
    x ∈ satP (idS (A := A) (B := B)) p a ↔ x = ([], a) := by
  obtain ⟨d, m⟩ := x
  constructor
  · rintro (h | ⟨d', m', h, n, c', hc⟩ | ⟨d', e, ⟨y, h⟩, n, c', hc⟩ | ⟨ω, h, -⟩)
    · simpa [idS] using h
    · simp only [idS, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hc
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases d with _ | ⟨z, d⟩
      · simp only [List.nil_append, List.cons.injEq, Sigma.mk.injEq] at hc
        obtain ⟨⟨rfl, -⟩, -⟩ := hc
        rfl
      · simp at hc
    · simp [idS] at h
  · intro h
    exact .inl (by simpa [idS] using h)

/-- **Right unit**: the identity client, served by `t`. -/
theorem linkS_idS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    linkS t idS = mapStore (Equiv.prodPUnit S).symm (dropTrap (sat t)) := by
  refine obsTriple_ext (fun σ a x => ?_) (fun σ a x => ?_) (fun σ a x => ?_)
  · obtain ⟨s, ⟨⟩⟩ := σ
    simp only [linkS, mapStore, dropTrap, sat, Set.mem_image, Set.mem_ofPred_eq, Equiv.symm_symm,
      Equiv.prodPUnit_apply]
    constructor
    · rintro (⟨rs, s₁, e, hr, ⟨y, he⟩, rfl⟩ | ⟨rs, s₁, a₀, c, hr, hp, hc, rfl⟩ | ⟨ω, hω, -⟩)
      · simp only [Prod.mk.injEq] at he
        obtain ⟨hs, rfl⟩ := he
        obtain ⟨⟨a₁, c, y₁⟩, rfl, h₁⟩ := List.map_eq_singleton_iff.1 hs
        simp only [Sigma.mk.injEq, heq_eq_eq] at h₁
        obtain ⟨rfl, rfl⟩ := h₁
        refine ⟨(c, .ret y₁ s₁), ⟨rounds_singleton_iff.1 hr, by simp⟩, ?_⟩
        simp [mapEnd, linkEnd]
      · obtain ⟨h₁, rfl⟩ := Prod.mk.inj (satP_idS.1 hp)
        obtain rfl := served_eq_nil.1 h₁
        obtain rfl := rounds_nil_iff.1 hr
        exact ⟨(c, .div), ⟨hc, by simp⟩, by simp [mapEnd]⟩
      · simp [idS] at hω
    · rintro ⟨⟨c, e⟩, ⟨he, hne⟩, rfl⟩
      rcases e with ⟨y, s₁⟩ | _ | _
      · exact .inl ⟨[(a, c, y)], s₁, .ret y PUnit.unit, .cons he (.nil _), ⟨y, rfl⟩,
          by simp [mapEnd, linkEnd]⟩
      · exact absurd rfl hne
      · exact .inr (.inl ⟨[], s, a, c, .nil _, satP_idS.2 rfl, he, by simp [mapEnd]⟩)
  · obtain ⟨s, ⟨⟩⟩ := σ
    simp only [linkS, mapStore, dropTrap, sat, Set.mem_ofPred_eq, Equiv.symm_symm,
      Equiv.prodPUnit_apply]
    constructor
    · rintro ⟨rs, s₁, a₀, c, hr, hp, hc, hx⟩
      obtain ⟨h₁, rfl⟩ := Prod.mk.inj (satP_idS.1 hp)
      obtain rfl := served_eq_nil.1 h₁
      obtain rfl := rounds_nil_iff.1 hr
      obtain ⟨x₁, x₂⟩ := x
      simp only [servedLog_nil, List.nil_append] at hx
      subst hx
      exact hc
    · intro hx
      exact ⟨[], s, a, x.1, .nil _, satP_idS.2 rfl, hx, rfl⟩
  · obtain ⟨s, ⟨⟩⟩ := σ
    simp only [linkS, mapStore, dropTrap, sat, Set.mem_ofPred_eq, Equiv.symm_symm,
      Equiv.prodPUnit_apply]
    constructor
    · rintro (⟨rs, s₁, a₀, ω', hr, hp, hω', hk⟩ | ⟨ω', hω', -⟩)
      · obtain ⟨h₁, rfl⟩ := Prod.mk.inj (satP_idS.1 hp)
        obtain rfl := served_eq_nil.1 h₁
        obtain rfl := rounds_nil_iff.1 hr
        have : x = ω' := stream_ext fun k => by simpa using hk k
        exact this ▸ hω'
      · simp [idS] at hω'
    · intro hx
      exact .inl ⟨[], s, a, x, .nil _, satP_idS.2 rfl, hx, fun k => by simp⟩

/-- The rounds of the identity server: each round makes its served call. -/
theorem rounds_idS {p p' : PUnit.{u + 1}} {rs : List (A × List (Call (sig1 A B)) × (B ⊕ PUnit))}
    (h : Rounds (idS (A := A) (B := B)) p rs p') : servedLog rs = served rs := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    obtain ⟨y, hy⟩ := h
    simp only [Prod.mk.injEq, End.ret.injEq] at hy
    obtain ⟨rfl, rfl, -⟩ := hy
    simp [ih]

/-- The identity server serves every list of calls. -/
theorem rounds_idS_of (d : List (Call (sig1 A B))) :
    ∃ rs, Rounds (idS (A := A) (B := B)) PUnit.unit rs PUnit.unit ∧ served rs = d ∧
      servedLog rs = d := by
  induction d with
  | nil => exact ⟨[], .nil _, rfl, rfl⟩
  | cons x d ih =>
    obtain ⟨rs, hr, h₁, h₂⟩ := ih
    exact ⟨(x.1, [x], x.2) :: rs, .cons ⟨x.2, rfl⟩ hr, by simp [h₁], by simp [h₂]⟩

/-- **Left unit**: the client `u`, served by the identity server. -/
theorem idS_linkS (u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})) :
    linkS idS u = mapStore (Equiv.punitProd S).symm (sat u) := by
  refine obsTriple_ext (fun σ a x => ?_) (fun σ a x => ?_) (fun σ a x => ?_)
  · obtain ⟨⟨⟩, s⟩ := σ
    simp only [linkS, mapStore, sat, Set.mem_image, Set.mem_ofPred_eq, Equiv.symm_symm,
      Equiv.punitProd_apply]
    constructor
    · rintro (⟨rs, ⟨⟩, e, hr, he, rfl⟩ | ⟨rs, s₁, a₀, c, hr, hp, ⟨y, hc⟩, rfl⟩ |
        ⟨ω, hω, l, st, n, hs, hl, rfl⟩)
      · refine ⟨(served rs, e), he, ?_⟩
        rw [rounds_idS hr]
        rcases e with _ | _ | _ <;> rfl
      · simp at hc
      · obtain ⟨y, hy⟩ := hs.step n
        simp only [Prod.mk.injEq] at hy
        simp [hl n le_rfl] at hy
    · rintro ⟨⟨d, e⟩, he, rfl⟩
      obtain ⟨rs, hr, h₁, h₂⟩ := rounds_idS_of (A := A) (B := B) d
      refine .inl ⟨rs, PUnit.unit, e, hr, h₁ ▸ he, ?_⟩
      rw [h₂]
      rcases e with _ | _ | _ <;> rfl
  · obtain ⟨⟨⟩, s⟩ := σ
    simp only [linkS, mapStore, sat, Set.mem_ofPred_eq, Equiv.symm_symm, Equiv.punitProd_apply]
    constructor
    · rintro ⟨rs, s₁, a₀, c, hr, hp, hc, hx⟩
      obtain ⟨rfl, h₂⟩ := Prod.mk.inj (satP_idS.1 hc)
      obtain ⟨x₁, x₂⟩ := x
      simp only [List.append_nil] at hx h₂
      subst hx h₂
      rw [rounds_idS hr]
      exact hp
    · intro hx
      obtain ⟨rs, hr, h₁, h₂⟩ := rounds_idS_of (A := A) (B := B) x.1
      exact ⟨rs, PUnit.unit, x.2, [], hr, h₁ ▸ hx, satP_idS.2 rfl, by simp [h₂]⟩
  · obtain ⟨⟨⟩, s⟩ := σ
    simp only [linkS, mapStore, sat, Set.mem_ofPred_eq, Equiv.symm_symm, Equiv.punitProd_apply]
    constructor
    · rintro (⟨rs, s₁, a₀, ω', hr, hp, hω', hk⟩ | ⟨ω', hω', l, st, hs, -, hk⟩)
      · simp [idS] at hω'
      · have hl : ∀ k, l k = [ω' k] := fun k => by
          obtain ⟨y, hy⟩ := hs.step k
          simp only [Prod.mk.injEq, End.ret.injEq] at hy
          obtain ⟨h₁, h₂, -⟩ := hy
          rw [h₁, ← h₂]
        have hlt : ∀ k, logTake l k = streamTake ω' k := fun k => by
          induction k with
          | zero => rfl
          | succ k ih => rw [logTake_succ, ih, hl, streamTake_succ]
        have : x = ω' := stream_ext fun k => by simpa [hlt] using hk k
        exact this ▸ hω'
    · intro hx
      refine .inr ⟨x, hx, fun k => [x k], fun _ => PUnit.unit, ⟨rfl, fun k => ⟨(x k).2, rfl⟩⟩,
        fun n => ⟨n, ?_⟩, fun k => ?_⟩
      all_goals
        have hlt : ∀ k, logTake (fun k => [x k]) k = streamTake x k := fun k => by
          induction k with
          | zero => rfl
          | succ k ih => rw [logTake_succ, ih, streamTake_succ]
      · simp [hlt]
      · simp [hlt]

/-! ## When the unit laws hold before saturation -/

theorem linkS_idS_eq_sat_iff {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} :
    linkS t idS = mapStore (Equiv.prodPUnit S).symm (sat t) ↔ StratSession.NoPlainTrap t := by
  rw [linkS_idS, (mapStore_injective _).eq_iff, dropTrap_eq_iff]
  rfl

theorem linkS_idS_eq_iff {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} :
    linkS t idS = mapStore (Equiv.prodPUnit S).symm t ↔
      StratSession.NoPlainTrap t ∧ Saturated t := by
  rw [linkS_idS, (mapStore_injective _).eq_iff]
  constructor
  · intro h
    refine ⟨fun s a c hc => ?_, saturated_iff.2 (congrArg (fun t => t.2.1) h)⟩
    have : (c, End.trap) ∈ (dropTrap (sat t)).1 s a := by rw [h]; exact hc
    exact this.2 rfl
  · rintro ⟨hn, hs⟩
    rw [show sat t = t from hs, dropTrap_eq_iff.2 hn]

theorem idS_linkS_eq_iff {u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})} :
    linkS idS u = mapStore (Equiv.punitProd S).symm u ↔ Saturated u := by
  rw [idS_linkS, (mapStore_injective _).eq_iff]
  rfl

/-! ## Counterexamples -/

theorem linkS_trapT_idS_ne :
    linkS (trapT (E := E)) idS ≠ mapStore (Equiv.prodPUnit _).symm (sat trapT) := by
  rw [Ne, linkS_idS_eq_sat_iff]
  exact fun h => h PUnit.unit PUnit.unit [] rfl

theorem idS_linkS_callDivT_ne :
    linkS idS callDivT.{u} ≠ mapStore (Equiv.punitProd _).symm callDivT.{u} := by
  rw [Ne, idS_linkS_eq_iff, saturated_iff]
  intro h
  have : (([] : List (Call (sig1 PUnit.{u + 1} PUnit.{u + 1}))), PUnit.unit) ∈
      satP callDivT.{u} PUnit.unit PUnit.unit :=
    .inr (.inr (.inl ⟨_, _, rfl, _, [], rfl⟩))
  rw [h] at this
  exact this

end Silmaril.Proofs.Games.Abstract.SessionLinkAssoc
