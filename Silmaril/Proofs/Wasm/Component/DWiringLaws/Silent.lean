module

public import Silmaril.Proofs.Wasm.Component.DWiringLaws.Basic

/-!
# Hidden chatter below any handler is silent chatter

`chatter_iff_silent`: for any handler `h`, an infinite interaction of `h` with
`σ` whose visible part stays `s` exists iff `SilentChatter h σ s`.

* Along a run of `h` with upper moves only, every event other than the first
  and the last is silent (`run_silent`): after an upper move, the handler is
  idle, or about to return an answer it computed without a call (`HGood`), or
  it can only call below (`HStuck`).
* `silentChatter_of_chatter`: after at most two hidden moves of an infinite
  chatter, `σ` is running; every later move is silent.
* `chatter_of_silentChatter`: from the running position, the handler runs the
  silent events of the infinite play one by one.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringLaws

open Silmaril.Games Silmaril.Wasm.Component

universe u

variable {E F G : Sig.{u}}

/-- The states of a handler between silent rounds. -/
def HGood (h : Handler E F) (x : h.toReduction.State) : Prop :=
  x = .idle ∨ ∃ q r, h q = .pure r ∧ x = .run q (.pure r)

/-- The states of a handler without an upper move. -/
def HStuck (h : Handler E F) (x : h.toReduction.State) : Prop :=
  ∀ e y, ¬ h.toReduction.toLTS.step x (some (.inr e)) y

theorem stuck_call {h : Handler E F} {q : F.Op} {m : E.Op} {k : E.Ar m → Prog E (F.Ar q)} :
    HStuck h (.run q (.call m k)) := by
  intro e y hs
  cases hs with
  | ret hc =>
    change Prog.call m k = Prog.pure _ at hc
    cases hc

theorem step_any {h : Handler E F} {x y : h.toReduction.State} {e : Ev F}
    (hs : h.toReduction.toLTS.step x (some (.inr e)) y) : HGood h y ∨ HStuck h y := by
  cases hs with
  | ask q =>
    change HGood h (.run q (h q)) ∨ HStuck h (.run q (h q))
    cases hq : h q with
    | pure r => exact .inl (.inr ⟨q, r, hq, rfl⟩)
    | call m k => exact .inr stuck_call
  | ret _ => exact .inl (.inl rfl)

theorem step_good {h : Handler E F} {x y : h.toReduction.State} {e : Ev F} (hx : HGood h x)
    (hs : h.toReduction.toLTS.step x (some (.inr e)) y) :
    (Silent h e ∧ HGood h y) ∨ HStuck h y := by
  rcases hx with rfl | ⟨q, r, hq, rfl⟩
  · cases hs with
    | ask q =>
      change (Silent h (.ask q) ∧ HGood h (.run q (h q))) ∨ HStuck h (.run q (h q))
      cases hq : h q with
      | pure r => exact .inl ⟨⟨r, hq⟩, .inr ⟨q, r, hq, rfl⟩⟩
      | call m k => exact .inr stuck_call
  · cases hs with
    | ret hc =>
      change Prog.pure r = Prog.pure _ at hc
      cases hc
      exact .inl ⟨hq, .inl rfl⟩

theorem run_nil {h : Handler E F} {x y : h.toReduction.State}
    (hr : h.toReduction.toLTS.Run x [] y) : y = x := by
  match hr with
  | .nil _ => rfl
  | .tau hs _ => cases hs with | tau hc => exact hc.elim

theorem step_of_run_cons {h : Handler E F} {x z : h.toReduction.State} {o : Move E F}
    {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, h.toReduction.toLTS.step x (some o) y ∧ h.toReduction.toLTS.Run y s z := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hr
  rw [run_nil h₁] at h₂
  exact ⟨x₂, h₂, h₃⟩

theorem not_stuck_of_run {h : Handler E F} {x z : h.toReduction.State} (l : List (Ev F))
    (b : Ev F) (hr : h.toReduction.toLTS.Run x ((l ++ [b]).map Sum.inr) z) : ¬ HStuck h x := by
  cases l with
  | nil =>
    obtain ⟨y, hs, -⟩ := step_of_run_cons hr
    exact fun hx => hx _ _ hs
  | cons c l =>
    obtain ⟨y, hs, -⟩ := step_of_run_cons hr
    exact fun hx => hx _ _ hs

theorem run_silent_good {h : Handler E F} : ∀ {x y : h.toReduction.State} (l : List (Ev F))
    (b : Ev F), HGood h x → h.toReduction.toLTS.Run x ((l ++ [b]).map Sum.inr) y →
      ∀ e ∈ l, Silent h e
  | _, _, [], _, _, _ => by simp
  | _, _, e :: l, b, hx, hr => by
    obtain ⟨x', hs, hr'⟩ := step_of_run_cons (s := (l ++ [b]).map Sum.inr) hr
    rcases step_good hx hs with ⟨he, hx'⟩ | hst
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact he
      · exact run_silent_good l b hx' hr' e' he'
    · exact (not_stuck_of_run l b hr' hst).elim

/-- **Silent events.** Along a run of a handler with upper moves only, every
event other than the first and the last is silent. -/
theorem run_silent {h : Handler E F} {x y : h.toReduction.State} {a b : Ev F}
    {l : List (Ev F)} (hr : h.toReduction.toLTS.Run x ((a :: (l ++ [b])).map Sum.inr) y) :
    ∀ e ∈ l, Silent h e := by
  obtain ⟨x', hs, hr'⟩ := step_of_run_cons (s := (l ++ [b]).map Sum.inr) hr
  rcases step_any hs with hx' | hst
  · exact run_silent_good l b hx' hr'
  · exact (not_stuck_of_run l b hr' hst).elim

/-- **Hidden chatter below a handler is silent chatter.** -/
theorem silentChatter_of_chatter {h : Handler E F} {σ : DStrategy F G}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler h) σ) {s : List (Move E G)}
    (hp : ∀ m, i.p m = s) : SilentChatter h σ s := by
  obtain ⟨-, ht, -, hlim⟩ := i.chatter_inf hp
  have hz : ∀ m, Zip (i.s m) (i.t m) s := fun m => hp m ▸ i.zip m
  have hws : ∀ m, ∃ ws : List (Ev F),
      i.s m = i.s 0 ++ ws.map Sum.inr ∧ i.t m = i.t 0 ++ ws.map Sum.inl := fun m =>
    ext_hidden (hz 0) (hz m) (i.mono_s.le (Nat.zero_le m)) (i.mono_t.le (Nat.zero_le m))
  choose ws hwsS hwsT using hws
  obtain ⟨y₀, hy₀⟩ := Strategy.mem_ofHandler.1 (i.mem_s 0)
  have hrun : ∀ m, ∃ y, h.toReduction.toLTS.Run y₀ ((ws m).map Sum.inr) y := by
    intro m
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 (i.mem_s m)
    rw [hwsS m] at hy
    obtain ⟨z, hz₁, hz₂⟩ := LTS.Run.of_append hy
    rw [run_det hz₁ hy₀] at hz₂
    exact ⟨y, hz₂⟩
  have hlenT : ∀ m, (i.t m).length = (i.t 0).length + (ws m).length := by
    intro m; rw [hwsT m]; simp
  obtain ⟨M₁, -, hM₁⟩ := i.mono_t.unbounded_ge ht ((i.t 0).length + 2) 0
  rw [hlenT M₁] at hM₁
  obtain ⟨e₁, e₂, rest, hw₁⟩ : ∃ e₁ e₂ rest, ws M₁ = e₁ :: e₂ :: rest := by
    rcases hw : ws M₁ with _ | ⟨e₁, _ | ⟨e₂, rest⟩⟩
    · rw [hw] at hM₁; simp only [List.length_nil] at hM₁; omega
    · rw [hw] at hM₁; simp only [List.length_cons, List.length_nil] at hM₁; omega
    · exact ⟨e₁, e₂, rest, rfl⟩
  obtain ⟨bM, hbM⟩ := σ.toStrategy.legal (i.mem_t M₁)
  rw [hwsT M₁, hw₁] at hbM
  obtain ⟨b₀, hb₀, hrest⟩ := Path.of_append hbM
  simp only [List.map_cons] at hrest
  obtain ⟨ws', hpre, hne, g, hg⟩ : ∃ ws', ws' <+: ws M₁ ∧ ws' ≠ [] ∧
      ∃ g, Path .idle (i.t 0 ++ ws'.map Sum.inl) (.run g) := by
    cases hrest with
    | cons hst₁ hrest =>
      cases hrest with
      | cons hst₂ _ =>
        cases hst₁ with
        | call g q =>
          cases hst₂ with
          | reply _ _ r =>
            exact ⟨[.ask q, .ans q r], by rw [hw₁]; simp, by simp, g,
              by simpa using hb₀.append (.cons (.call g q) (.cons (.reply g q r) (.nil _)))⟩
        | reply g q r =>
          exact ⟨[.ans q r], by rw [hw₁]; simp, by simp, g,
            by simpa using hb₀.append (Path.single (.reply g q r))⟩
  refine ⟨_, hlim, i.t 0 ++ ws'.map Sum.inl,
    ⟨M₁, by rw [hwsT M₁]; exact (List.prefix_append_right_inj _).2 (hpre.map _)⟩, ⟨g, hg⟩, ?_,
    i.s 0 ++ ws'.map Sum.inr, (Strategy.ofHandler h).of_prefix (i.mem_s M₁)
      (by rw [hwsS M₁]; exact (List.prefix_append_right_inj _).2 (hpre.map _)),
    zip_append_sync (hz 0) ws'⟩
  intro w x hx
  obtain ⟨M, hM⟩ := hx
  obtain ⟨M', hMM', hlen'⟩ :=
    i.mono_t.unbounded_ge ht ((i.t 0 ++ ws'.map Sum.inl ++ w ++ [x]).length + 1) M
  obtain ⟨r, hr⟩ := hM.trans (i.mono_t.le hMM')
  have hlM' := hlenT M'
  rw [hwsT M'] at hr
  simp only [List.append_assoc] at hr
  have hr' := List.append_cancel_left hr
  obtain ⟨a₁, a₂, ha, h₁, h₂⟩ := List.map_eq_append_iff.1 hr'.symm
  have ha₁ : a₁ = ws' := List.map_injective_iff.2 Sum.inl_injective h₁
  subst ha₁
  obtain ⟨b₁, b₂, rfl, hu, h₃⟩ := List.map_eq_append_iff.1 h₂
  obtain ⟨c₁, c₂, rfl, hx, hr''⟩ := List.map_eq_append_iff.1 h₃
  obtain ⟨e, rfl⟩ : ∃ e, c₁ = [e] := by
    rcases c₁ with _ | ⟨e, _ | _⟩ <;> simp at hx
    exact ⟨e, rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  refine ⟨e, hx.symm, ?_⟩
  have hlr : 0 < c₂.length := by
    have h₄ := congrArg List.length ha
    have h₅ := congrArg List.length hr''
    have h₆ := congrArg List.length hu
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at *
    omega
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_pos hlr
  obtain ⟨yM, hyM⟩ := hrun M'
  rw [ha] at hyM
  have hsplit : (a :: as ++ (b₁ ++ ([e] ++ c :: cs))).map Sum.inr =
      (a :: ((as ++ b₁ ++ [e]) ++ [c])).map (Sum.inr (α := Ev E)) ++ cs.map Sum.inr := by
    simp
  rw [hsplit] at hyM
  obtain ⟨z, hz', -⟩ := LTS.Run.of_append hyM
  exact run_silent hz' e (by simp)

/-- **Silent chatter is hidden chatter below the handler.** -/
theorem chatter_of_silentChatter {h : Handler E F} {σ : DStrategy F G} {s : List (Move E G)}
    (hc : SilentChatter h σ s) :
    ∃ i : DStrategy.InfInteraction (DStrategy.ofHandler h) σ, ∀ m, i.p m = s := by
  obtain ⟨I, hI, t₀, ht₀, ⟨g₀, hg₀⟩, htr, u, hu, hz⟩ := hc
  have hII := σ.inf_isInf hI
  let L := t₀.length
  let T : Chain (Move F G) := fun m => hII.seq (L + m)
  have hTmem : ∀ m, T m ∈ I := fun m => hII.seq_mem _
  have hTlen : ∀ m, (T m).length = L + m := fun m => hII.seq_length _
  have hTmono : T.Mono := fun m => hII.seq_mono (L + m)
  have hTpre : ∀ m, t₀ <+: T m := fun m =>
    hII.prefix_of_length_le ht₀ (hTmem m) (by rw [hTlen]; omega)
  have htail : ∀ d, t₀ ++ d ∈ I → nR d = 0 := by
    intro d
    induction d using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton d x ih =>
      intro hd
      rw [← List.append_assoc] at hd
      obtain ⟨e, rfl, -⟩ := htr d x hd
      have : nR (d ++ [Sum.inl e]) = nR d := by simp [nR]
      rw [this]
      exact ih (hII.of_prefix hd (List.prefix_append _ _))
  let es : ℕ → List (Ev F) := fun m => ((T m).drop L).filterMap Sum.getLeft?
  have hTes : ∀ m, T m = t₀ ++ (es m).map Sum.inl := by
    intro m
    obtain ⟨d, hd⟩ := hTpre m
    have hdrop : (T m).drop L = d := by rw [← hd]; simp [L]
    have hd0 := htail d (hd ▸ hTmem m)
    rw [show es m = d.filterMap Sum.getLeft? by simp only [es, hdrop], ← eq_map_inl hd0]
    exact hd.symm
  have hes0 : es 0 = [] := by
    have hl := hTlen 0
    rw [hTes 0] at hl
    simpa [L] using hl
  have hstep : ∀ m, ∃ e, es (m + 1) = es m ++ [e] ∧ Silent h e := by
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
  have hP : ∀ m, ∃ y, h.toReduction.toLTS.Run .idle (u ++ (es m).map Sum.inr) y ∧
      ∃ b, Path .idle (T m) b ∧ ((y = .idle ∧ ∃ g, b = .run g) ∨
        ∃ g q r, h q = .pure r ∧ y = .run q (.pure r) ∧ b = .wait g q) := by
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
      rcases hinv with ⟨rfl, g, rfl⟩ | ⟨g, q, r, hq, rfl, rfl⟩
      · cases hst with
        | call _ q =>
          obtain ⟨r, hr⟩ := he
          refine ⟨.run q (.pure r), hrun.append ?_, .wait g q, hbT, .inr ⟨g, q, r, hr, rfl, rfl⟩⟩
          have := LTS.Run.of_step (L := h.toReduction.toLTS)
            (Reduction.Step.ask (R := h.toReduction) q)
          simpa [Handler.toReduction, hr] using this
      · cases hst with
        | reply _ _ r' =>
          have hrr : r' = r := by
            have he' : h q = .pure r' := he
            rw [hq] at he'
            cases he'
            rfl
          subst hrr
          refine ⟨.idle, hrun.append ?_, .run g, hbT, .inl ⟨rfl, g, rfl⟩⟩
          exact LTS.Run.of_step (L := h.toReduction.toLTS) (Reduction.Step.ret (R := h.toReduction)
            (q := q) (c := .pure r') (r := r') rfl)
  choose y hy using hP
  have hmono_s : Chain.Mono (fun m => u ++ (es m).map Sum.inr) := fun m => by
    obtain ⟨e, hes, -⟩ := hstep m
    simp only [hes, List.map_append, ← List.append_assoc]
    exact List.prefix_append _ _
  have hmem_s : ∀ m, u ++ (es m).map Sum.inr ∈ Strategy.ofHandler h :=
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

/-- **Hidden chatter below a handler is exactly silent chatter.** -/
theorem chatter_iff_silent {h : Handler E F} {σ : DStrategy F G} {s : List (Move E G)} :
    (∃ i : DStrategy.InfInteraction (DStrategy.ofHandler h) σ, ∀ m, i.p m = s) ↔
      SilentChatter h σ s :=
  ⟨fun ⟨i, hi⟩ => silentChatter_of_chatter i hi, chatter_of_silentChatter⟩

/-- **Divergence with a handler below**: a divergence of `σ` through the
handler, or silent chatter. -/
theorem div_ofHandler_comp_iff (h : Handler E F) (σ : DStrategy F G) :
    ((DStrategy.ofHandler h).comp σ).div =
      {p | (∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler h ∧ v ∈ σ.div) ∨ SilentChatter h σ p} := by
  ext p
  rw [DStrategy.mem_div_comp, DStrategy.ofHandler_div]
  constructor
  · rintro (⟨s, t, hz, ⟨hs, -⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩)
    · exact hs.elim
    · exact .inl ⟨s, t, hz, hs, ht⟩
    · exact .inr (silentChatter_of_chatter i hi)
  · rintro (⟨s, t, hz, hs, ht⟩ | hc)
    · exact .inl ⟨s, t, hz, .inr ⟨hs, ht⟩⟩
    · exact .inr (chatter_of_silentChatter hc)

end Silmaril.Proofs.Wasm.Component.DWiringLaws
