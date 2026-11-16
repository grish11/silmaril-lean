module

public import Silmaril.Proofs.Wasm.Component.DWiringLaws.Basic
public import Silmaril.Wasm.Component.DWiring.Thms

/-!
# Trap chatter below `widenH` is exactly hidden chatter

`chatter_iff`: an infinite interaction of `widenH n` with `σ` whose visible
part stays `s` exists iff `TrapChatter n σ s`.

* `trapChatter_of_chatter`: by `chatter_widenH`, the interaction plays an
  eventually-trap infinite play of `σ`; a stage of it at which `σ` is running
  (at most one hidden move after any stage) gives the lined-up position.
* `chatter_of_trapChatter`: from the running position `t₀`, the handler runs
  the trap events of the infinite play one by one (out-of-range calls are
  answered `none` at once), alternating between the idle state and a state
  about to return `none`. The resulting chains form the infinite interaction.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringLaws

open Silmaril.Games Silmaril.Wasm.Component

variable {n : Nat} {G : Sig.{0}}

/-- After `t₀`, an eventually-trap infinite play moves below only. -/
theorem tail_inl {I : Set (List (Move sigU G))} (hI : IsInfPlay I) {t₀ : List (Move sigU G)}
    (htr : ∀ w x, t₀ ++ w ++ [x] ∈ I → ∃ e, x = .inl e ∧ IsTrap n e) :
    ∀ d, t₀ ++ d ∈ I → nR d = 0 := by
  intro d
  induction d using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton d x ih =>
    intro hd
    rw [← List.append_assoc] at hd
    obtain ⟨e, rfl, -⟩ := htr d x hd
    have : nR (d ++ [Sum.inl e]) = nR d := by simp [nR]
    rw [this]
    exact ih (hI.of_prefix hd (List.prefix_append _ _))

/-- **Hidden chatter below `widenH` is trap chatter.** -/
theorem trapChatter_of_chatter {σ : DStrategy sigU G}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ)
    {s : List (Move (sigN n) G)} (hp : ∀ m, i.p m = s) : TrapChatter n σ s := by
  obtain ⟨hlim, t₁, ht₁, htr⟩ := chatter_widenH i hp
  obtain ⟨-, ht, -, -⟩ := i.chatter_inf hp
  obtain ⟨N, hN⟩ := ht₁
  obtain ⟨M, hNM, hlen⟩ := i.mono_t.unbounded_ge ht ((i.t N).length + 1) N
  have hzN : Zip (i.s N) (i.t N) s := hp N ▸ i.zip N
  have hzM : Zip (i.s M) (i.t M) s := hp M ▸ i.zip M
  obtain ⟨ws, hsM, htM⟩ := ext_hidden hzN hzM (i.mono_s.le hNM) (i.mono_t.le hNM)
  obtain ⟨e, ws, rfl⟩ : ∃ e ws', ws = e :: ws' := by
    cases ws with
    | nil =>
      simp only [htM, List.map_nil, List.append_nil] at hlen
      omega
    | cons e ws' => exact ⟨e, ws', rfl⟩
  have htail : ∀ t₀, t₁ <+: t₀ → ∀ w x, t₀ ++ w ++ [x] ∈ i.t.lim →
      ∃ e, x = .inl e ∧ IsTrap n e := by
    rintro t₀ ⟨d, rfl⟩ w x hx
    exact htr (d ++ w) x (by simpa [List.append_assoc] using hx)
  obtain ⟨bM, hbM⟩ := σ.toStrategy.legal (i.mem_t M)
  rw [htM] at hbM
  obtain ⟨b, hb, hrest⟩ := Path.of_append hbM
  simp only [List.map_cons] at hrest
  cases hrest with
  | cons hst _ =>
    cases b with
    | idle => cases hst
    | run g =>
      exact ⟨_, hlim, i.t N, Chain.mem_lim_self _ N, ⟨g, hb⟩, htail _ hN, i.s N, i.mem_s N, hzN⟩
    | wait g f =>
      cases hst with
      | reply _ _ r =>
        refine ⟨_, hlim, i.t N ++ [.inl (.ans f r)], ⟨M, ?_⟩,
          ⟨g, hb.append (Path.single (.reply g f r))⟩,
          htail _ (hN.trans (List.prefix_append _ _)), i.s N ++ [.inr (.ans f r)],
          (Strategy.ofHandler _).of_prefix (i.mem_s M) ?_, ?_⟩
        · rw [htM]; simp
        · rw [hsM]; simp
        · simpa using zip_append_sync hzN [.ans f r]

/-- **Trap chatter is hidden chatter below `widenH`.** -/
theorem chatter_of_trapChatter {σ : DStrategy sigU G} {s : List (Move (sigN n) G)}
    (h : TrapChatter n σ s) :
    ∃ i : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ, ∀ m, i.p m = s := by
  obtain ⟨I, hI, t₀, ht₀, ⟨g₀, hg₀⟩, htr, u, hu, hz⟩ := h
  have hII := σ.inf_isInf hI
  let L := t₀.length
  let T : Chain (Move sigU G) := fun m => hII.seq (L + m)
  have hTmem : ∀ m, T m ∈ I := fun m => hII.seq_mem _
  have hTlen : ∀ m, (T m).length = L + m := fun m => hII.seq_length _
  have hTmono : T.Mono := fun m => hII.seq_mono (L + m)
  have hTpre : ∀ m, t₀ <+: T m := fun m =>
    hII.prefix_of_length_le ht₀ (hTmem m) (by rw [hTlen]; omega)
  let es : ℕ → List (Ev sigU) := fun m => ((T m).drop L).filterMap Sum.getLeft?
  have hTes : ∀ m, T m = t₀ ++ (es m).map Sum.inl := by
    intro m
    obtain ⟨d, hd⟩ := hTpre m
    have hdrop : (T m).drop L = d := by rw [← hd]; simp [L]
    have hd0 := tail_inl hII htr d (hd ▸ hTmem m)
    rw [show es m = d.filterMap Sum.getLeft? by simp only [es, hdrop], ← eq_map_inl hd0]
    exact hd.symm
  have hes0 : es 0 = [] := by
    have hl := hTlen 0
    rw [hTes 0] at hl
    simpa [L] using hl
  have hstep : ∀ m, ∃ e, es (m + 1) = es m ++ [e] ∧ IsTrap n e := by
    intro m
    obtain ⟨d, hd⟩ := hTmono m
    have hl := congrArg List.length hd
    rw [List.length_append, hTlen, hTlen] at hl
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 (by omega : d.length = 1)
    have hx : t₀ ++ (es m).map Sum.inl ++ [x] ∈ I := by
      rw [← hTes m, hd]; exact hTmem _
    obtain ⟨e, rfl, he⟩ := htr _ x hx
    refine ⟨e, ?_, he⟩
    have h₁ := hTes (m + 1)
    rw [← hd, hTes m, List.append_assoc, List.append_cancel_left_eq] at h₁
    apply List.map_injective_iff.2 Sum.inl_injective
    rw [← h₁, List.map_append]
    rfl
  have hP : ∀ m, ∃ y, (widenH n).toReduction.toLTS.Run .idle (u ++ (es m).map Sum.inr) y ∧
      ∃ b, Path .idle (T m) b ∧ ((y = .idle ∧ ∃ g, b = .run g) ∨
        ∃ g q, n ≤ q.1 ∧ y = .run q (.pure none) ∧ b = .wait g q) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hu
      have hT0 : T 0 = t₀ := by rw [hTes 0, hes0]; simp
      refine ⟨y, by rw [hes0]; simpa using hy, .run g₀, hT0 ▸ hg₀, .inl ⟨?_, g₀, rfl⟩⟩
      have hpy := run_path hy
      generalize hpos : spos y = a at hpy
      obtain ⟨c, -, hc⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle hpy hg₀
      cases hc
      cases y with
      | idle => rfl
      | run => cases hpos
      | wait => cases hpos
    | succ m ih =>
      obtain ⟨y, hrun, b, hb, hinv⟩ := ih
      obtain ⟨e, hes, he⟩ := hstep m
      obtain ⟨b', hbT⟩ := σ.toStrategy.legal (σ.inf_sub hI (hTmem (m + 1)))
      have hb' := hbT
      rw [hTes (m + 1), hes, List.map_append, ← List.append_assoc, ← hTes m] at hb'
      obtain ⟨b'', hb'', hst⟩ := Path.concat_iff.1 hb'
      rw [← hb.det hb''] at hst
      rw [hes, List.map_append, ← List.append_assoc]
      rcases hinv with ⟨rfl, g, rfl⟩ | ⟨g, q, hq, rfl, rfl⟩
      · cases hst with
        | call _ q =>
          have hwq : (widenH n) q = .pure none := by
            simp [widenH, Nat.not_lt.2 he]
          refine ⟨.run q (.pure none), hrun.append ?_, .wait g q, hbT, .inr ⟨g, q, he, rfl, rfl⟩⟩
          have := LTS.Run.of_step (L := (widenH n).toReduction.toLTS)
            (Reduction.Step.ask (R := (widenH n).toReduction) q)
          simpa [Handler.toReduction, hwq] using this
      · cases hst with
        | reply _ _ r =>
          cases he
          refine ⟨.idle, hrun.append ?_, .run g, hbT, .inl ⟨rfl, g, rfl⟩⟩
          exact LTS.Run.of_step (L := (widenH n).toReduction.toLTS)
            (Reduction.Step.ret (R := (widenH n).toReduction) (q := q) (c := .pure none)
              (r := none) rfl)
  choose y hy using hP
  have hmono_s : Chain.Mono (fun m => u ++ (es m).map Sum.inr) := fun m => by
    obtain ⟨e, hes, -⟩ := hstep m
    simp only [hes, List.map_append, ← List.append_assoc]
    exact List.prefix_append _ _
  have hmem_s : ∀ m, u ++ (es m).map Sum.inr ∈ Strategy.ofHandler (widenH n) :=
    fun m => Strategy.mem_ofHandler.2 ⟨y m, (hy m).1⟩
  have hTu : T.Unbounded := fun k => ⟨k, by rw [hTlen]; omega⟩
  refine ⟨{ s := fun m => u ++ (es m).map Sum.inr
            t := T
            p := fun _ => s
            zip := fun m => by
              show Zip _ (T m) _
              rw [hTes m]
              exact zip_append_sync hz (es m)
            mem_s := hmem_s
            mem_t := fun m => σ.inf_sub hI (hTmem m)
            mono_s := hmono_s
            mono_t := hTmono
            mono_p := fun _ => List.prefix_refl _
            unbounded := fun k => ⟨k, by rw [hTlen]; omega⟩
            lim_s := fun hu' => lim_mem_inf_ofHandler hmono_s hu' hmem_s
            lim_t := fun _ => by rw [lim_eq_of_mem hII hTmem hTu]; exact hI }, fun _ => rfl⟩

/-- **Hidden chatter below `widenH` is exactly trap chatter.** -/
theorem chatter_iff {σ : DStrategy sigU G} {s : List (Move (sigN n) G)} :
    (∃ i : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ, ∀ m, i.p m = s) ↔
      TrapChatter n σ s :=
  ⟨fun ⟨i, hi⟩ => trapChatter_of_chatter i hi, chatter_of_trapChatter⟩

end Silmaril.Proofs.Wasm.Component.DWiringLaws
