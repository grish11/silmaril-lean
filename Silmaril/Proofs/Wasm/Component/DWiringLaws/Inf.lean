module

public import Silmaril.Proofs.Wasm.Component.DWiringLaws.Basic
public import Silmaril.Wasm.Component.DWiring.Thms

/-!
# Infinite plays through handlers

* `inf_ofHandler_comp`: with a one-call handler `h` below `σ`, the infinite
  plays of the composite are the infinite plays of `σ` seen through `h`
  (`ThroughBelow`). One way, `lim_t_of_oneCall`; the other way, the chains
  lined up with an infinite play form an infinite interaction: the handler side
  converges to an infinite play of the handler (`lim_mem_inf_ofHandler`), and
  the side of `σ` to the infinite play itself (`lim_eq_of_mem`).
* `inf_comp_ofHandler_allCall`: with a handler `h` that always calls above
  `δ`, the infinite plays of the composite are the infinite plays of `δ` seen
  through `h` (`ThroughAbove`). Such a handler makes at least one move below per
  move above, up to one (`count_allCall`), so `δ` moves forever when the
  visible play does (`unbounded_s`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringLaws

open Silmaril.Games Silmaril.Wasm.Component

universe u

variable {E F G : Sig.{u}}

/-! ## Handlers that always call -/

/-- The counting invariant of a handler that always calls. -/
def Inv₂ (h : Handler E F) : h.toReduction.State → ℕ → ℕ → Prop
  | .idle, a, b => b ≤ a
  | .run _ c, a, b => (b ≤ a + 1 ∧ ∃ m k, c = .call m k ∧ ∀ n, ∃ r, k n = .pure r) ∨
      (b + 1 ≤ a ∧ ∃ r, c = .pure r)
  | .wait _ _ k, a, b => b ≤ a ∧ ∀ n, ∃ r, k n = .pure r

theorem inv₂_le {h : Handler E F} {x : h.toReduction.State} {a b : ℕ} (hx : Inv₂ h x a b) :
    b ≤ a + 1 := by
  cases x with
  | idle => exact Nat.le_succ_of_le hx
  | run q c => rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩ <;> omega
  | wait q m k => exact Nat.le_succ_of_le hx.1

theorem inv₂_step {h : Handler E F} (hh : AllCall h) {x y : h.toReduction.State}
    {o : Option (Move E F)} (hs : h.toReduction.toLTS.step x o y) {a b : ℕ}
    (hx : Inv₂ h x a b) : Inv₂ h y (a + nL o.toList) (b + nR o.toList) := by
  cases hs with
  | ask q =>
    simp only [Option.toList_some, nL_inr, nL_nil, nR_inr, nR_nil, Inv₂]
    exact .inl ⟨by simp only [Inv₂] at hx; omega, hh q⟩
  | tau hc => exact hc.elim
  | call hc =>
    simp only [Option.toList_some, nL_inl, nL_nil, nR_inl, nR_nil, Inv₂]
    change _ = Prog.call _ _ at hc
    subst hc
    rcases hx with ⟨hab, m', k', hc, hk⟩ | ⟨-, r, hr⟩
    · cases hc
      exact ⟨by omega, hk⟩
    · cases hr
  | resume q m k n =>
    simp only [Option.toList_some, nL_inl, nL_nil, nR_inl, nR_nil, Inv₂]
    exact .inr ⟨by simp only [Inv₂] at hx; omega, hx.2 n⟩
  | ret hc =>
    simp only [Option.toList_some, nL_inr, nL_nil, nR_inr, nR_nil, Inv₂]
    change _ = Prog.pure _ at hc
    subst hc
    rcases hx with ⟨-, m, k, hc, -⟩ | ⟨hab, -⟩
    · cases hc
    · omega

theorem inv₂_run {h : Handler E F} (hh : AllCall h) : ∀ {x y : h.toReduction.State}
    {s : List (Move E F)}, h.toReduction.toLTS.Run x s y →
    ∀ {a b : ℕ}, Inv₂ h x a b → Inv₂ h y (a + nL s) (b + nR s)
  | _, _, _, .nil _, _, _, hx => by simpa using hx
  | _, _, _, .tau hs hr, _, _, hx => by
    simpa using inv₂_run hh hr (by simpa using inv₂_step hh hs hx)
  | _, _, _, .vis (o := o) (s := s) hs hr, _, _, hx => by
    have := inv₂_run hh hr (inv₂_step hh hs hx)
    cases o <;> simp only [Option.toList_some, nL_inl, nL_inr, nR_inl, nR_inr, nL_nil,
      nR_nil] at this ⊢ <;> (convert this using 1; omega)

/-- A handler that always calls makes at least one move below per move above,
up to one. -/
theorem count_allCall {h : Handler E F} (hh : AllCall h) {t : List (Move E F)}
    (ht : t ∈ Strategy.ofHandler h) : nR t ≤ nL t + 1 := by
  obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.1 ht
  have := inv₂_le (inv₂_run hh hr (a := 0) (b := 0) (show 0 ≤ 0 from le_rfl))
  simpa using this

/-- With a handler that always calls on top, the strategy below moves forever
when the visible part does. -/
theorem unbounded_s {X : Sig.{u}} {h : Handler E F} (hh : AllCall h) {δ : DStrategy X E}
    (i : DStrategy.InfInteraction δ (DStrategy.ofHandler h)) (hp : i.p.Unbounded) :
    i.s.Unbounded := by
  intro k
  by_contra hk
  push Not at hk
  obtain ⟨n, hn⟩ := hp (2 * k + 2)
  have hz := zip_counts (i.zip n)
  have hc := count_allCall hh (i.mem_t n)
  have hp := length_eq (i.p n)
  have hs := length_eq (i.s n)
  have ht := length_eq (i.t n)
  have := hk n
  omega

theorem allCall_narrowH (k : Nat) : AllCall (narrowH k) :=
  fun _ => ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩

theorem allCall_splitH (e : Nat) : AllCall (splitH e) := by
  intro q
  unfold splitH
  split
  · exact ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩
  · exact ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩

/-! ## Infinite plays through handlers -/

theorem unbounded_of_zip {X Y Z : Sig.{u}} {s : Chain (Move X Y)} {t : Chain (Move Y Z)}
    {p : Chain (Move X Z)} (hz : ∀ m, Zip (s m) (t m) (p m)) (hp : p.Unbounded) :
    ∀ k, ∃ m, k ≤ (s m).length + (t m).length := fun k => by
  obtain ⟨m, hm⟩ := hp k
  exact ⟨m, hm.trans (zip_length_le (hz m))⟩

/-- **Infinite plays with a one-call handler below.** -/
theorem inf_ofHandler_comp {E F G : Sig.{0}} {h : Handler E F} (hh : OneCall h)
    (σ : DStrategy F G) :
    ((DStrategy.ofHandler h).comp σ).inf = {K | ∃ I ∈ σ.inf, ThroughBelow h I K} := by
  ext K
  constructor
  · rintro ⟨i, hpu, rfl⟩
    obtain ⟨-, hlim⟩ := DStrategy.lim_t_of_oneCall hh i hpu
    exact ⟨_, hlim, i.s, i.t, i.p, i.zip, i.mem_s, Chain.mem_lim_self _, i.mono_s, i.mono_t,
      i.mono_p, hpu, rfl⟩
  · rintro ⟨I, hI, u, t, s, hz, hu, ht, mu, mt, ms, hsu, rfl⟩
    exact ⟨{ s := u, t := t, p := s, zip := hz, mem_s := hu
             mem_t := fun m => σ.inf_sub hI (ht m)
             mono_s := mu, mono_t := mt, mono_p := ms
             unbounded := unbounded_of_zip hz hsu
             lim_s := fun huu => lim_mem_inf_ofHandler mu huu hu
             lim_t := fun htu => (lim_eq_of_mem (σ.inf_isInf hI) ht htu) ▸ hI }, hsu, rfl⟩

/-- **Infinite plays with a handler that always calls above.** -/
theorem inf_comp_ofHandler_allCall {X : Sig.{u}} {h : Handler E F} (hh : AllCall h)
    (δ : DStrategy X E) :
    (δ.comp (DStrategy.ofHandler h)).inf = {J | ∃ K ∈ δ.inf, ThroughAbove h K J} := by
  ext J
  constructor
  · rintro ⟨i, hpu, rfl⟩
    exact ⟨_, i.lim_s (unbounded_s hh i hpu), i.s, i.t, i.p, i.zip, Chain.mem_lim_self _,
      i.mem_t, i.mono_s, i.mono_t, i.mono_p, hpu, rfl⟩
  · rintro ⟨K, hK, s, w, p, hz, hs, hw, ms, mw, mp, hpu, rfl⟩
    exact ⟨{ s := s, t := w, p := p, zip := hz, mem_s := fun m => δ.inf_sub hK (hs m)
             mem_t := hw, mono_s := ms, mono_t := mw, mono_p := mp
             unbounded := unbounded_of_zip hz hpu
             lim_s := fun hsu => (lim_eq_of_mem (δ.inf_isInf hK) hs hsu) ▸ hK
             lim_t := fun hwu => lim_mem_inf_ofHandler mw hwu hw }, hpu, rfl⟩

end Silmaril.Proofs.Wasm.Component.DWiringLaws
