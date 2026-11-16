module

public import Silmaril.Proofs.Wasm.Component.DWiringChatter2.Basic
public import Silmaril.Proofs.Wasm.Component.DWiringChatter2.Route
public import Silmaril.Wasm.Component.DWiringChatter.Thms
public import Silmaril.Games.DPair.Thms

/-!
# Chatter between an environment and the node above it, routed

`chatter_extTop_iff` (`Silmaril.Wasm.Component.DWiringChatter.Thms`) reduces
hidden chatter of `D` with `extTop e N` to an infinite play `I` of `D`
chattering with `J`, an infinite play `K` of copycat beside `N` seen through
`splitH e`. Here `K` and `J` are eliminated (`chatter_ext_iff`).

* Chatter is eventually pure synchronisation (`chatter_tail_iff`): after an
  aligned pair `s₀ ∈ I`, `c₀ ∈ J`, both continue by the same moves `w` at `D`'s
  upper interface.
* Through `splitH e`, the pairing play under `c₀ ++ w` is
  `c₀.map (splitRoute e) ++ w` (`route_prefix_of_zip`), a member of `K`.
* During `w` copycat receives nothing from outside, and a copycat play has at
  most one more lower move than upper moves (`cntL_le_of_mem_id`). So the
  moves `w` cannot all go to copycat: the round in progress after `c₀` is a
  round of `N` (`side_eq_true`), and `w` goes to `N`. Its half of `K` is then
  unbounded, an infinite play `L` of `N`.
* Conversely, from `I`, `L` and the prefix, the chains
  `c₀.map (splitRoute e) ++ w` and `c₀ ++ w` along the infinite trace of the
  `w` give `K` and `J` (`chatter_of_extChatter`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter2

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Games.DStrategy (InfInteraction)

universe u

/-! ## Splitting appended plays -/

section Split

variable {E F₁ F₂ : Sig.{u}}

theorem halves_append (b : Bool) (x y : List (Move E (F₁ ⊕ₛ F₂))) :
    Split.halves b (x ++ y) = ((Split.halves b x).1 ++ (Split.halves (Split.side b x) y).1,
      (Split.halves b x).2 ++ (Split.halves (Split.side b x) y).2) := by
  induction x generalizing b with
  | nil => rfl
  | cons o x ih =>
    rcases o with l | (q | ⟨q, r⟩)
    · cases b <;> simp [Split.halves, Split.side, ih]
    · rcases q with q | q <;> simp [Split.halves, Split.side, ih]
    · rcases q with q | q <;> simp [Split.halves, Split.side, ih]

theorem halves_map_inl (b : Bool) (w : List (Ev E)) :
    Split.halves (F₁ := F₁) (F₂ := F₂) b (w.map .inl) =
      if b then ([], w.map .inl) else (w.map .inl, []) := by
  induction w with
  | nil => cases b <;> rfl
  | cons l w ih => cases b <;> simp_all [Split.halves]

/-- After a play of the pairing where the right component's round is in
progress, lower moves go to the right half. -/
theorem halves_append_inl_of_side {x : List (Move E (F₁ ⊕ₛ F₂))} (h : Split.side false x = true)
    (w : List (Ev E)) :
    Split.halves false (x ++ w.map .inl) =
      ((Split.halves false x).1, (Split.halves false x).2 ++ w.map .inl) := by
  rw [halves_append, h, halves_map_inl]
  simp

end Split

/-! ## Copycat moves below at most once more than above -/

section Copy

variable {E : Sig.{u}}

theorem cntL_le_of_prefix_double {x : List (Move E E)} :
    ∀ {w : List (Ev E)}, x <+: Ev.double w → cntL x ≤ cntR x + 1
  | [], h => by rw [List.prefix_nil.1 h]; simp
  | y :: w, h => by
    rw [Ev.double_cons] at h
    obtain ⟨t, ht⟩ := h
    rcases List.append_eq_append_iff.1 ht with ⟨a', hy, -⟩ | ⟨b', rfl, hb⟩
    · have : cntL x ≤ cntL (Ev.copy y) := cntL_mono ⟨a', hy.symm⟩
      cases y <;> simp only [Ev.copy] at this <;> simp at this <;> omega
    · have := cntL_le_of_prefix_double (x := b') ⟨t, hb.symm⟩
      cases y <;> simp [Ev.copy] <;> omega

/-- A copycat play has at most one more lower move than upper moves. -/
theorem cntL_le_of_mem_id {x : List (Move E E)} (h : x ∈ Strategy.id E) : cntL x ≤ cntR x + 1 := by
  obtain ⟨w, -, hw⟩ := Strategy.mem_id.1 h
  exact cntL_le_of_prefix_double hw

end Copy

/-! ## Lower moves from related positions -/

section Lower

variable {E F G : Sig.{u}}

/-- Two positions in which the same lower moves are allowed. -/
def Corr : Pos E F → Pos E G → Prop
  | .idle, .idle => True
  | .run _, .run _ => True
  | .wait _ m, .wait _ m' => m = m'
  | _, _ => False

theorem lower_path : ∀ (w : List (Ev E)) {x : Pos E F} {x' : Pos E G} {z : Pos E F},
    Path x (w.map .inl) z → Corr x x' → ∃ z', Path x' (w.map .inl) z'
  | [], _, x', _, _, _ => ⟨x', .nil _⟩
  | l :: w, x, x', z, h, hc => by
    cases h with
    | cons hs hp =>
      cases hs with
      | call q m =>
        cases x' with
        | run q' =>
          obtain ⟨z', hz'⟩ := lower_path w hp (x' := .wait q' m) rfl
          exact ⟨z', .cons (.call q' m) hz'⟩
        | idle => exact hc.elim
        | wait _ _ => exact hc.elim
      | reply q m n =>
        cases x' with
        | wait q' m' =>
          cases hc
          obtain ⟨z', hz'⟩ := lower_path w hp (x' := .run q') trivial
          exact ⟨z', .cons (.reply q' m n) hz'⟩
        | idle => exact hc.elim
        | run _ => exact hc.elim

theorem corr_of_rel {x : Pos E (F ⊕ₛ G)} {x₁ : Pos E F} {x₂ : Pos E G}
    (h : Split.Rel x true x₁ x₂) : Corr x₂ x := by
  cases h <;> trivial

end Lower

/-! ## From chatter to the routed form -/

variable {X : Sig.{0}} {e : Nat} {D : DStrategy X sigU} {N : DStrategy sigU sigU}
  {p : List (Move X sigU)}

theorem map_route_append_inl (c : List (Move sigU sigU)) (w : List (Ev sigU)) :
    (c ++ w.map Sum.inl).map (splitRoute e) = c.map (splitRoute e) ++ w.map Sum.inl := by
  simp [Function.comp_def, splitRoute]

theorem not_endsAsk {c : List (Move sigU sigU)} {w : List (Ev sigU)} (hw : w ≠ []) :
    ¬ EndsAsk (c ++ w.map .inl) := by
  rintro ⟨c', q, h⟩
  obtain ⟨w, l, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
  rw [List.concat_eq_append, List.map_append, ← List.append_assoc] at h
  have := (List.append_inj' h rfl).2
  simp at this

/-- **The round in progress is `N`'s.** If the pairing play `x` is followed by
more lower moves than copycat's half of it has moves plus one, they cannot all
go to copycat. -/
theorem side_eq_true {x : List (Move sigU (sigU ⊕ₛ sigU))} {w : List (Ev sigU)}
    (hw : x.length + 2 ≤ w.length)
    (h : (Split.halves false (x ++ w.map .inl)).1 ∈ Strategy.id sigU) :
    Split.side false x = true := by
  cases hs : Split.side false x with
  | true => rfl
  | false =>
    rw [halves_append, hs, halves_map_inl] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have h₁ := cntL_le_of_mem_id h
    simp only [cntL_append, cntL_map_inl, cntR_append, cntR_map_inl] at h₁
    have h₂ := length_eq_cnt (Split.halves false x).1
    have h₃ := Split.halves_length false x
    omega

/-- **Chatter is eventually `D` and `N` exchanging moves.** In the closed form
of `chatter_extTop_iff`, after an aligned prefix `s₀ ∈ I`, `c₀ ∈ J`, a round of
`N` is in progress and `I` and `K` continue by the same moves `w` at `D`'s
upper interface. -/
theorem tail_of_chatter {I : Set (List (Move X sigU))} (hI : I ∈ D.inf)
    {K : Set (List (Move sigU (sigU ⊕ₛ sigU)))}
    (hK : IsInfPlay K ∧ K ⊆ ((Strategy.id sigU).pair N.toStrategy).plays ∧
      (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf))
    {J : Set (List (Move sigU sigU))} (hTA : ThroughAbove (splitH e) K J) (hC : Chatter I J p) :
    ∃ s₀ c₀, Zip s₀ c₀ p ∧ c₀ ∈ J ∧ Split.side false (c₀.map (splitRoute e)) = true ∧
      ∀ k, ∃ w : List (Ev sigU), k ≤ w.length ∧ s₀ ++ w.map .inr ∈ I ∧
        c₀.map (splitRoute e) ++ w.map .inl ∈ K := by
  obtain ⟨hKi, hKs, -⟩ := id hK
  have hJmem : J ∈ (DStrategy.extTop e N).inf := by
    rw [DStrategy.inf_extTop]
    exact ⟨K, hK, hTA⟩
  have hJ := (DStrategy.extTop e N).inf_isInf hJmem
  obtain ⟨s₀, -, c₀, hc₀, hz, ht⟩ := (chatter_tail_iff (D.inf_isInf hI) hJ).1 hC
  obtain ⟨sch, wch, pch, hzc, hsK, hwh, -, -, -, -, hJlim⟩ := hTA
  have hroute : ∀ w : List (Ev sigU), w ≠ [] → c₀ ++ w.map .inl ∈ J →
      c₀.map (splitRoute e) ++ w.map .inl ∈ K := by
    intro w hw hc
    rw [hJlim] at hc
    obtain ⟨n, hn⟩ := hc
    obtain ⟨a', w', ha', hw', hz'⟩ := (hzc n).of_prefix hn
    have ha'K : a' ∈ K := hKi.of_prefix (hsK n) ha'
    rcases route_prefix_of_zip hz' ((Strategy.ofHandler (splitH e)).of_prefix (hwh n) hw')
      (Strategy.mem_pair.1 (hKs ha'K)).1 with hp | hask
    · rw [map_route_append_inl] at hp
      exact hKi.of_prefix ha'K hp
    · exact absurd hask (not_endsAsk hw)
  have hlong : ∀ k, ∃ w : List (Ev sigU), k ≤ w.length ∧ s₀ ++ w.map .inr ∈ I ∧
      c₀.map (splitRoute e) ++ w.map .inl ∈ K := by
    intro k
    obtain ⟨w, hk, hs, hc⟩ := ht (k + 1)
    refine ⟨w, by omega, hs, hroute w ?_ hc⟩
    rintro rfl
    simp at hk
  have hside : Split.side false (c₀.map (splitRoute e)) = true := by
    obtain ⟨w, hk, -, hK⟩ := hlong ((c₀.map (splitRoute e)).length + 2)
    exact side_eq_true hk (Strategy.mem_pair.1 (hKs hK)).2.1
  exact ⟨s₀, c₀, hz, hc₀, hside, hlong⟩

/-- **Copycat is eventually silent.** In the closed form of
`chatter_extTop_iff`, copycat's projection of `K` is bounded and `N`'s is an
infinite trace. -/
theorem copycat_silent {I : Set (List (Move X sigU))} (hI : I ∈ D.inf)
    {K : Set (List (Move sigU (sigU ⊕ₛ sigU)))}
    (hK : IsInfPlay K ∧ K ⊆ ((Strategy.id sigU).pair N.toStrategy).plays ∧
      (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf))
    {J : Set (List (Move sigU sigU))} (hTA : ThroughAbove (splitH e) K J) (hC : Chatter I J p) :
    ¬ IsInfPlay (Split.infL K) ∧ IsInfPlay (Split.infR K) := by
  obtain ⟨s₀, c₀, -, -, hside, hlong⟩ := tail_of_chatter hI hK hTA hC
  refine ⟨fun hL => ?_, (Split.isInfPlay_infR_iff hK.1).2 fun k => ?_⟩
  · obtain ⟨u, ⟨a, ha, hu⟩, hl⟩ :=
      hL.unbounded ((Split.halves false (c₀.map (splitRoute e))).1.length + 1)
    obtain ⟨w, hk, -, hw⟩ := hlong a.length
    have hpre := (Split.halves_prefix (hK.1.prefix_of_length_le ha hw
      (by simp only [List.length_append, List.length_map]; omega)) false).1
    rw [halves_append_inl_of_side hside] at hpre
    have := (hu.trans hpre).length_le
    simp only at this
    omega
  · obtain ⟨w, hk, -, hK'⟩ := hlong k
    refine ⟨_, hK', ?_⟩
    rw [halves_append_inl_of_side hside]
    simp only [List.length_append, List.length_map]
    omega

/-- **Chatter, routed (forwards).** -/
theorem extChatter_of_chatter (h : ∃ i : InfInteraction D (DStrategy.extTop e N), ∀ m, i.p m = p) :
    ∃ I ∈ D.inf, ∃ L ∈ N.inf, ExtChatter e I L p := by
  obtain ⟨I, hI, K, hK, J, hTA, hC⟩ := DStrategy.chatter_extTop_iff.1 h
  have hJmem : J ∈ (DStrategy.extTop e N).inf := by
    rw [DStrategy.inf_extTop]
    exact ⟨K, hK, hTA⟩
  obtain ⟨s₀, c₀, hz, hc₀, hside, hlong⟩ := tail_of_chatter hI hK hTA hC
  have hinfR := (copycat_silent hI hK hTA hC).2
  refine ⟨I, hI, Split.infR K, hK.2.2 hinfR, s₀, c₀, hz,
    (DStrategy.extTop e N).toStrategy.legal ((DStrategy.extTop e N).inf_sub hJmem hc₀), hside,
    ?_, fun k => ?_⟩
  · obtain ⟨w, -, -, hK'⟩ := hlong 0
    have := (Strategy.mem_pair.1 (hK.2.1 hK')).2.1
    rwa [halves_append_inl_of_side hside] at this
  · obtain ⟨w, hk, hs, hK'⟩ := hlong k
    refine ⟨w, hk, hs, _, hK', ?_⟩
    rw [halves_append_inl_of_side hside]

/-! ## From the routed form to chatter -/

/-- **Chatter, routed (backwards).** -/
theorem chatter_of_extChatter {I : Set (List (Move X sigU))} (hI : I ∈ D.inf)
    {L : Set (List (Move sigU sigU))} (hL : L ∈ N.inf) (h : ExtChatter e I L p) :
    ∃ i : InfInteraction D (DStrategy.extTop e N), ∀ m, i.p m = p := by
  obtain ⟨s₀, c₀, hz, hc₀, hside, hu₀, ht⟩ := h
  have hIi := D.inf_isInf hI
  have hLi := N.inf_isInf hL
  have hW : IsInfPlay {w : List (Ev sigU) | s₀ ++ w.map .inr ∈ I ∧
      (Split.halves false (c₀.map (splitRoute e))).2 ++ w.map .inl ∈ L} := by
    refine ⟨fun hw hvw => ⟨hIi.of_prefix hw.1 ((List.prefix_append_right_inj _).2 (hvw.map _)),
      hLi.of_prefix hw.2 ((List.prefix_append_right_inj _).2 (hvw.map _))⟩, ?_, ?_⟩
    · have key : ∀ {v w : List (Ev sigU)}, s₀ ++ v.map .inr ∈ I → s₀ ++ w.map .inr ∈ I →
          v.length ≤ w.length → v <+: w := by
        intro v w hv hw hl
        have h₁ := (List.prefix_append_right_inj _).1
          (hIi.prefix_of_length_le hv hw (by simpa using hl))
        simpa [List.filterMap_map, Function.comp_def] using h₁.filterMap Sum.getRight?
      intro v w hv hw
      rcases le_total v.length w.length with hl | hl
      · exact .inl (key hv.1 hw.1 hl)
      · exact .inr (key hw.1 hv.1 hl)
    · intro k
      obtain ⟨w, hk, hs, hl⟩ := ht k
      exact ⟨w, ⟨hs, hl⟩, hk⟩
  obtain ⟨ws₀, hws₀, hzs⟩ := exists_zip_route (e := e) hc₀
  let a : Chain (Move sigU (sigU ⊕ₛ sigU)) := fun n => c₀.map (splitRoute e) ++ (hW.seq n).map .inl
  let cc : Chain (Move sigU sigU) := fun n => c₀ ++ (hW.seq n).map .inl
  have hmem := hW.seq_mem
  have hlen := hW.seq_length
  have ha_mono : a.Mono := fun n => (List.prefix_append_right_inj _).2 ((hW.seq_mono n).map _)
  have hc_mono : cc.Mono := fun n => (List.prefix_append_right_inj _).2 ((hW.seq_mono n).map _)
  have ha_pair : ∀ n, a n ∈ (Strategy.id sigU).pair N.toStrategy := by
    intro n
    refine Strategy.mem_pair.2 ⟨?_, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := legal_route (e := e) hc₀
      obtain ⟨y₁, y₂, -, h₂, hr⟩ := Split.halves_path hy (Split.Rel.idle false)
      rw [hside] at hr
      obtain ⟨z, hz⟩ := N.toStrategy.legal (N.inf_sub hL (hmem n).2)
      obtain ⟨y₂', h₂', hrest⟩ := Path.of_append hz
      rw [← Path.det h₂ h₂'] at hrest
      obtain ⟨z', hz'⟩ := lower_path _ hrest (corr_of_rel hr)
      exact ⟨z', hy.append hz'⟩
    · show (Split.halves false (a n)).1 ∈ _
      rw [halves_append_inl_of_side hside]
      exact hu₀
    · show (Split.halves false (a n)).2 ∈ _
      rw [halves_append_inl_of_side hside]
      exact N.inf_sub hL (hmem n).2
  have ha_unb : a.Unbounded := fun k => ⟨k, by simp [a, hlen]⟩
  have hc_unb : cc.Unbounded := fun k => ⟨k, by simp [cc, hlen]⟩
  have hK : a.lim ∈ ((DStrategy.id sigU).pair N).inf := by
    rw [DStrategy.inf_pair_id]
    refine ⟨Chain.isInfPlay_lim ha_mono ha_unb, ?_, fun _ => ?_⟩
    · rintro q ⟨n, hq⟩
      exact ((Strategy.id sigU).pair N.toStrategy).of_prefix (ha_pair n) hq
    · have : Split.infR a.lim = L := by
        ext u
        constructor
        · rintro ⟨a', ⟨n, ha'⟩, hu⟩
          have := (Split.halves_prefix ha' false).2
          simp only [a, halves_append_inl_of_side hside] at this
          exact hLi.of_prefix (hmem n).2 (hu.trans this)
        · intro hu
          refine ⟨a u.length, Chain.mem_lim_self a _, ?_⟩
          simp only [a, halves_append_inl_of_side hside]
          exact hLi.prefix_of_length_le hu (hmem _).2 (by simp [hlen])
      rw [this]
      exact hL
  have hJ : cc.lim ∈ (DStrategy.extTop e N).inf := by
    rw [DStrategy.extTop, DStrategy.inf_comp_ofHandler_allCall (allCall_splitH e)]
    exact ⟨a.lim, hK, a, fun _ => ws₀, cc, fun n => zip_append_inl hzs _,
      fun n => Chain.mem_lim_self a n, fun _ => hws₀, ha_mono, fun _ => List.prefix_refl _,
      hc_mono, hc_unb, rfl⟩
  refine DStrategy.InfInteraction.chatter_iff.2 ⟨I, hI, cc.lim, hJ, fun k => ?_⟩
  refine ⟨s₀ ++ (hW.seq k).map .inr, (hmem k).1, cc k, Chain.mem_lim_self cc k, ?_,
    zip_append_sync hz _⟩
  simp only [cc, List.length_append, List.length_map, hlen]
  omega

end Silmaril.Proofs.Wasm.Component.DWiringChatter2
