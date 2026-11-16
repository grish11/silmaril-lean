module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Games
public import Silmaril.Proofs.Wasm.Component.Reference.MultiIR

/-!
# The plays of a simple component's IR denotation

For a simple component `c` whose module has an instance `I`, every play of
`c.toComp.den (modSem P)` is made of export rounds: complete rounds `twos L`, possibly followed
by one pending export question (`den_shape`). The complete rounds are read back, layer by
layer (`atSizes`, the export handler, the environment, the core node, `modSem`, `core3Sem`'s
export handler, the instance), as specification rounds at the Core stores the instance threads
(`SpecRounds`, `specRounds_of_den`):

* a round answered at once is a trap of the export handler: an ill-typed call (or a payload of
  the wrong kind), with the store unchanged;
* every other round is a typed call whose lowered arguments run the core export from the
  current store `s` to an outcome `r ∈ coreAt P I x.core xs s`, the IR answer being the lift of
  `r`; when the lift returns results `ws`, the call is a returned call `RetAt` to the next
  store.

The converse direction (specification rounds are plays) is `MultiIR`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Component.Reference

/-! ## Empty lower interfaces -/

theorem noInl_sigN0 {F : Sig.{0}} (p : List (Move (sigN 0) F)) : NoInl p := by
  intro e _
  cases e with
  | ask m => exact m.1.elim0
  | ans m _ => exact m.1.elim0

theorem noInl_sigN_nil {F : Sig.{0}} {n : Nat} (hn : n = 0) (p : List (Move (sigN n) F)) :
    NoInl p := by
  subst hn
  exact noInl_sigN0 p

theorem noInl_inst {I : Silmaril.Wasm.Game.ScalarInstance} (hI : I.imports = []) {F : Sig.{0}}
    (p : List (Move I.E F)) : NoInl p := by
  intro e _
  have key : ∀ m : I.E.Op, False := fun m => by
    have h : m.1.val < I.imports.length := m.1.isLt
    have h' : I.imports.length = 0 := by rw [hI]; rfl
    omega
  cases e with
  | ask m => exact key m
  | ans m _ => exact key m

/-- A handler answering every question at once has no lower moves. -/
theorem noInl_ofHandler_pure {E F : Sig.{0}} {h : Handler E F} (hp : ∀ q, ∃ a, h q = .pure a) :
    ∀ t ∈ Strategy.ofHandler h, NoInl t := by
  intro t ht
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
  have key : ∀ (t : List (Move E F)) (x y : h.toReduction.State),
      (match x with
        | .idle => True
        | .run _ c => ∃ a, c = .pure a
        | .wait _ _ _ => False) →
      h.toReduction.toLTS.Run x t y → NoInl t := by
    intro t
    induction t with
    | nil => intro _ _ _ _; exact .nil
    | cons m t ih =>
      intro x y hx hr
      obtain ⟨x', hs, hr'⟩ := run_cons_inv hr
      cases hs with
      | ask q => exact (ih _ y (hp q) hr').cons_inr
      | @call q c m' k hc =>
        obtain ⟨a, rfl⟩ := hx
        cases (hc : Prog.pure a = .call m' k)
      | resume => exact hx.elim
      | ret _ => exact (ih _ y trivial hr').cons_inr
  exact key t .idle y trivial hy

/-! ## The handlers -/

theorem oneShot_narrowH (k : Nat) : OneShot (narrowH k) :=
  fun q => .inr ⟨(q.1.val, q.2), fun r => r, rfl⟩

theorem oneShot_widenH (n : Nat) : OneShot (widenH n) := by
  intro q
  unfold widenH
  split
  · exact .inr ⟨_, fun r => r, rfl⟩
  · exact .inl ⟨none, rfl⟩

theorem oneShot_splitH (e : Nat) : OneShot (splitH e) := by
  intro q
  unfold splitH
  split
  · exact .inr ⟨.inl q, fun r => r, rfl⟩
  · exact .inr ⟨.inr (q.1 - e, q.2), fun r => r, rfl⟩

theorem oneShot_exportH (m : NumInstance) : OneShot (exportH m) := by
  intro q
  unfold exportH
  dsimp only
  split
  · split
    · exact .inr ⟨_, fun a => answerPayload a, rfl⟩
    · exact .inl ⟨none, rfl⟩
  · exact .inl ⟨none, rfl⟩

/-- The program of a wiring chain answers at once or by one call. -/
theorem runChain_oneShot (e : Nat) (tg : Target) :
    ∀ (ch : List Adapter) (p : Payload),
      (∃ a, runChain ch (tg.prog e) p = .pure a) ∨
        ∃ f, ∃ k : Option Payload → Option Payload,
          runChain ch (tg.prog e) p = .call f fun r => .pure (k r)
  | [], p => by
    cases tg with
    | call r =>
      simp only [runChain, Target.prog]
      split
      · exact .inr ⟨_, fun r => r, rfl⟩
      · exact .inl ⟨none, rfl⟩
    | const res => exact .inl ⟨res, rfl⟩
  | ad :: ch, p => by
    simp only [runChain]
    split
    · exact .inl ⟨none, rfl⟩
    · rename_i a' _
      rcases runChain_oneShot e tg ch a' with ⟨a, ha⟩ | ⟨f, k, hk⟩
      · rw [ha]
        exact .inl ⟨_, rfl⟩
      · rw [hk]
        exact .inr ⟨f, fun r => (k r).bind ad.up, rfl⟩

theorem oneShot_implsH (e : Nat) (ims : List Impl) : OneShot (implsH e ims) := by
  intro q
  unfold implsH
  split
  · exact runChain_oneShot e _ _ _
  · exact .inl ⟨none, rfl⟩

theorem pure_maskH0 (q : sigU.Op) : ∃ a, maskH 0 q = .pure a := by
  refine ⟨none, ?_⟩
  simp [maskH, Target.prog]

theorem pure_implsN_nil (e t : Nat) (q : (sigN t).Op) : ∃ a, implsN e [] t q = .pure a :=
  ⟨none, rfl⟩

/-! ## Inverting `HRounds` -/

theorem hrounds_cons_inv {E F : Sig.{0}} {h : Handler E F} {q : F.Op} {a : F.Ar q}
    {up : List (Round F)} {low : List (Round E)} (H : HRounds h (⟨q, a⟩ :: up) low) :
    (h q = .pure a ∧ HRounds h up low) ∨
      ∃ q' k a' low', low = ⟨q', a'⟩ :: low' ∧ h q = .call q' k ∧ k a' = .pure a ∧
        HRounds h up low' := by
  cases H with
  | pure hq H' => exact .inl ⟨hq, H'⟩
  | call hq hk H' => exact .inr ⟨_, _, _, _, rfl, hq, hk, H'⟩

theorem hrounds_narrowH_inv (k : Nat) :
    ∀ {L : List (Round (sigN k))} {l : List (Round sigU)}, HRounds (narrowH k) L l →
      l = L.map Round.forget
  | [], _, H => by cases H; rfl
  | ⟨q, a⟩ :: L, l, H => by
    rcases hrounds_cons_inv H with ⟨hq, -⟩ | ⟨q', k', a', low', rfl, hq, hk, H'⟩
    · cases hq
    · simp only [narrowH, Prog.call.injEq] at hq
      obtain ⟨rfl, hk'⟩ := hq
      cases eq_of_heq hk'
      cases hk
      rw [hrounds_narrowH_inv k H']
      rfl

theorem hrounds_splitH0_inv :
    ∀ {l : List (Round sigU)} {l' : List (Round (sigU ⊕ₛ sigU))}, HRounds (splitH 0) l l' →
      l' = l.map (Round.inr (F₁ := sigU))
  | [], _, H => by cases H; rfl
  | ⟨q, a⟩ :: l, l', H => by
    rcases hrounds_cons_inv H with ⟨hq, -⟩ | ⟨q', k', a', low', rfl, hq, hk, H'⟩
    · simp [splitH] at hq
    · simp only [splitH, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hq
      cases hq
      injection hk with hk
      subst hk
      rw [hrounds_splitH0_inv H']
      rfl

/-! ## The instance -/

/-- Complete activations of the instance along rounds, threading the store. -/
inductive Acts (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (Round I.F) → Store Nat → Prop where
  | nil (s : Store Nat) : Acts P I s [] s
  | cons {s s₁ s₂ : Store Nat} {f : I.F.Op} {v : I.F.Ar f} {t : Thread} {r : Result}
      {l : List (Round I.F)} :
      Silmaril.Wasm.Game.Reach P (s, I.initThread f) (s₁, t) →
      Silmaril.Wasm.Game.ResultAt s₁ t r →
      Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some v →
      Acts P I s₁ l s₂ → Acts P I s (⟨f, v⟩ :: l) s₂

theorem acts_of_path {P : Profile} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ (l : List (Round I.F)) {s : Store Nat} {q : I.HState},
      I.Path P (.idle s) (twos l) q → ∃ s', Acts P I s l s'
  | [], s, _, _ => ⟨s, .nil s⟩
  | ⟨f, v⟩ :: l, s, q, h => by
    have h' : I.Path P (.idle s) (Sum.inr (.ask f) :: Sum.inr (.ans f v) :: twos l) q := h
    cases h' with
    | cons t₁ h₁ =>
      cases t₁ with
      | call =>
        cases h₁ with
        | cons t₂ h₂ =>
          cases t₂ with
          | oret run final answer =>
            obtain ⟨s', ha⟩ := acts_of_path l h₂
            exact ⟨s', .cons run final answer ha⟩

/-! ## The export handler of a simple component -/

/-- **The export handler of a simple component**: a trap at once, unless the question is a
well-typed call of an export with component values, which is one call of its core export on
the lowered values, the answer lifted. -/
theorem exportsH_shape {c : Simple} (hc : c.Good) (q : sigU.Op) :
    (exportsH c.mod.exports.length c.toComp.exports q = .pure none ∧
      ∀ (hj : q.1 < c.exports.length) (vs : List Silmaril.Wasm.Component.Val), q.2 = .vals vs →
        checkLower c.exports[q.1].ty.params vs = none) ∨
    ∃ (hj : q.1 < c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (xs : List Flat),
      q.2 = .vals vs ∧ checkLower c.exports[q.1].ty.params vs = some xs ∧
      exportsH c.mod.exports.length c.toComp.exports q =
        .call (c.exports[q.1].core, .flat xs)
          fun n => .pure (n.bind (Adapter.up (.lift c.exports[q.1].ty))) := by
  obtain ⟨j, p⟩ := q
  by_cases hj : j < c.exports.length
  · obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem hj)
    have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
    cases p with
    | vals vs =>
      have he := exportsH_toComp c hj vs hk
      cases hl : checkLower c.exports[j].ty.params vs with
      | none =>
        rw [hl] at he
        refine .inl ⟨he, fun _ vs' hv => ?_⟩
        cases hv
        exact hl
      | some xs =>
        rw [hl] at he
        exact .inr ⟨hj, vs, xs, rfl, hl, he⟩
    | flat xs =>
      refine .inl ⟨?_, fun _ _ hv => by cases hv⟩
      have hget : (c.toComp.exports.map Export.impl)[j]? =
          some ⟨[.lift c.exports[j].ty], .call c.exports[j].core⟩ := by
        simp [Simple.toComp, hj]
      simp only [exportsH, implsH, hget, Impl.prog, runChain, Adapter.down]
  · refine .inl ⟨?_, fun h => absurd h hj⟩
    have hget : (c.toComp.exports.map Export.impl)[j]? = none := by
      simp [Simple.toComp, Nat.le_of_not_lt hj]
    simp only [exportsH, implsH, hget]

/-! ## Specification rounds -/

/-- Host-free steps keep the function instances. -/
theorem internalP_funcs {P : Profile} {s s' : Store Nat} {t t' : Thread}
    (h : Silmaril.Wasm.Game.InternalP P (s, t) (s', t')) : s'.funcs = s.funcs := by
  obtain ⟨f', code', -, h⟩ := h
  have hl := Silmaril.Wasm.SingleThreaded.Step.framesLocal h
  simp only [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hl
  exact hl.1

/-- Host-free runs keep the function instances. -/
theorem reach_funcs {P : Profile} {x y : Store Nat × Thread} (h : Silmaril.Wasm.Game.Reach P x y) :
    y.1.funcs = x.1.funcs := by
  induction h with
  | refl => rfl
  | @tail b c _ hs ih => exact (internalP_funcs (s := b.1) (t := b.2) hs).trans ih

/-- **A round read as the specification at the store `s`**, ending at the store `s₁`: a trap at
once (an ill-typed call or a payload of the wrong kind), the store unchanged; or a typed call
whose lowered values run the core export to an outcome `r` of `coreAt` at `s`, answered by the
lift of `r`, and a returned call to `s₁` when the lift returns results. The run keeps the
function instances of the store. -/
def RoundSpec (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) (s : Store Nat) :
    Round sigU → Store Nat → Prop
  | ⟨(j, p), A⟩, s₁ =>
    (A = none ∧ s₁ = s ∧ ∀ (hj : j < c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
      p = .vals vs → checkLower c.exports[j].ty.params vs = none) ∨
    ∃ (hj : j < c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (xs : List Flat)
      (r : Option (List Flat)), p = .vals vs ∧ checkLower c.exports[j].ty.params vs = some xs ∧
      r ∈ coreAt P I c.exports[j].core xs s ∧
      A = (r.map Payload.flat).bind (Adapter.up (.lift c.exports[j].ty)) ∧
      (∀ ys ws, r = some ys → liftArgs c.exports[j].ty.results ys = some ws →
        RetAt P c I c.exports[j] vs s ws s₁) ∧ s₁.funcs = s.funcs

/-- Rounds read as the specification, threading the store. -/
inductive SpecRounds (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (Round sigU) → Prop where
  | nil (s : Store Nat) : SpecRounds P c I s []
  | cons {s s₁ : Store Nat} {x : Round sigU} {l : List (Round sigU)} :
      RoundSpec P c I s x s₁ → SpecRounds P c I s₁ l → SpecRounds P c I s (x :: l)

/-- **The handler chain read as the specification.** -/
theorem specRounds_of_chain {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ (l l₂ : List (Round sigU)) (l₄ : List (Round (CoreIface.sig (CoreModule.exports c.mod))))
      (l₅ : List (Round I.F)) (s s' : Store Nat),
      HRounds (exportsH c.mod.exports.length c.toComp.exports) l l₂ →
      HRounds (widenH (CoreModule.exports c.mod).length) l₂ l₄ →
      HRounds (exportH (instNum hI)) l₄ l₅ → Acts P I s l₅ s' → SpecRounds P c I s l
  | [], _, _, _, s, _, _, _, _, _ => .nil s
  | ⟨(j, p), A⟩ :: l, l₂, l₄, l₅, s, s', H₂, H₄, H₅, hA => by
    rcases hrounds_cons_inv H₂ with ⟨hq, H₂'⟩ | ⟨q₂, k₂, a₂, l₂', rfl, hq, hk, H₂'⟩
    · rcases exportsH_shape hc (j, p) with ⟨he, hn⟩ | ⟨hj, vs, xs, hp, hl, he⟩
      · rw [he] at hq
        cases hq
        exact .cons (.inl ⟨rfl, rfl, hn⟩) (specRounds_of_chain hc hI l l₂ l₄ l₅ s s' H₂' H₄ H₅ hA)
      · rw [he] at hq
        cases hq
    · rcases exportsH_shape hc (j, p) with ⟨he, -⟩ | ⟨hj, vs, xs, hp, hl, he⟩
      · rw [he] at hq
        cases hq
      rw [he] at hq
      simp only [Prog.call.injEq] at hq
      obtain ⟨rfl, hk'⟩ := hq
      cases eq_of_heq hk'
      cases hk
      obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem hj)
      obtain ⟨hkc, hget⟩ := List.getElem?_eq_some_iff.mp hcore
      have hxs : xs.map (·.type) = c.mod.exports[c.exports[j].core].2.params := by
        obtain ⟨hck, rfl⟩ := checkLower_eq hl
        rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget]
        exact lowerList_types _ _ hck
      rcases hrounds_cons_inv H₄ with ⟨hq₄, -⟩ | ⟨q₄, k₄, a₄, l₄', rfl, hq₄, hk₄, H₄'⟩
      · simp [widenH, CoreModule.exports, hkc] at hq₄
      have hw : widenH (CoreModule.exports c.mod).length (c.exports[j].core, Payload.flat xs) =
          .call (⟨c.exports[j].core, hkc⟩, .flat xs) fun r => .pure r := by
        simp [widenH, CoreModule.exports, hkc]
      rw [hw] at hq₄
      simp only [Prog.call.injEq] at hq₄
      obtain ⟨rfl, hk₄'⟩ := hq₄
      cases eq_of_heq hk₄'
      cases hk₄
      rcases hrounds_cons_inv H₅ with ⟨hq₅, -⟩ | ⟨q₅, k₅, v, l₅', rfl, hq₅, hk₅, H₅'⟩
      · rw [exportH_round hI hkc hxs] at hq₅
        cases hq₅
      rw [exportH_round hI hkc hxs] at hq₅
      simp only [Prog.call.injEq] at hq₅
      obtain ⟨rfl, hk₅'⟩ := hq₅
      cases eq_of_heq hk₅'
      cases hk₅
      cases hA with
      | @cons _ s₁ _ _ _ t res _ run final answer hA' =>
        have steps : Steps P Det.noHost (invoke s (I.addrs.getD c.exports[j].core 0)
            (xs.map ofFlat)) (t.config s₁) :=
          internalP_steps (H := Nat) run
        refine .cons (.inr ⟨hj, vs, xs, _, hp, hl, ⟨_, res, steps, final, rfl⟩, ?_, ?_,
          reach_funcs run⟩) (specRounds_of_chain hc hI l l₂' l₄' l₅' s₁ s' H₂' H₄' H₅' hA')
        · rw [answerPayload_of_ofResult? answer]
          rfl
        · intro ys ws hys hws
          obtain ⟨hck, rfl⟩ := checkLower_eq hl
          refine ⟨hck, ?_⟩
          cases res with
          | values cvs => exact ⟨t, cvs, ys, run, final, hys, hws⟩
          | trap => cases hys
          | throw a => cases hys

/-! ## The layers -/

/-- **Every play of the IR denotation of a simple component is complete export rounds, possibly
followed by one pending export question.** -/
theorem den_shape (C : CoreSem NumModule) (c : Simple)
    {p : List (Move (sigN 0) (sigN c.toComp.exports.length))} (hp : p ∈ c.toComp.den C) :
    (∃ L, p = twos L) ∨ ∃ q L, p = twos L ++ [.inr (.ask q)] :=
  shape_of_legal ((c.toComp.den C).legal hp) (noInl_sigN0 p)

/-- **Complete rounds of the IR denotation are specification rounds** from the instance's
store. -/
theorem specRounds_of_den {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {L : List (Round (sigN c.toComp.exports.length))}
    (h : twos L ∈ c.toComp.den (modSem P)) : SpecRounds P c I I.store (L.map Round.forget) := by
  -- `atSizes`
  unfold Comp.den atSizes at h
  obtain ⟨l, Hn, hl⟩ := hrounds_of_comp (oneShot_narrowH _) (fun s _ => noInl_sigN0 s) h
  rw [hrounds_narrowH_inv _ Hn] at hl
  -- the environment and the export handler
  have hN : ∀ t ∈ coreNode (modSem P) 0 c.mod [], NoInl t :=
    noInl_comp (noInl_ofHandler_pure (pure_implsN_nil 0 _))
  have hX : ∀ t ∈ ((Strategy.id sigU).pair (coreNode (modSem P) 0 c.mod [])).comp
      (Strategy.ofHandler (splitH 0)), NoInl t :=
    noInl_pair_comp (oneShot_splitH 0) (fun q f k hq => by
      simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hq
      cases hq
      exact ⟨_, rfl⟩) hN
  have hEnv : ∀ t ∈ envS (modSem P) c, NoInl t :=
    noInl_comp (noInl_ofHandler_pure pure_maskH0)
  have hU : ∀ t ∈ c.toComp.denU (modSem P), NoInl t := by
    rw [denU_toComp]
    exact noInl_comp hEnv
  have hl₁ := twos_of_comp_noInl hU hl
  rw [denU_toComp] at hl₁
  obtain ⟨l₂, H₂, hl₂⟩ := hrounds_of_comp (oneShot_implsH _ _) hEnv hl₁
  -- the mask below the extension
  have hl₃ := twos_of_comp_noInl hX hl₂
  -- the pairing below `splitH`
  have hpair : ∀ s ∈ (Strategy.id sigU).pair (coreNode (modSem P) 0 c.mod []),
      ∀ t ∈ Strategy.ofHandler (splitH 0), ∀ {p : List (Move sigU sigU)}, Zip s t p → NoInl s := by
    intro s hs t ht p hz
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
    refine noInl_of_pair hN hs fun q hm => ?_
    obtain ⟨q', k, hk⟩ := run_ask_mem (oneShot_splitH 0) t .idle y
      (show RunInv (splitH 0) .idle from trivial) hy _ (zip_inr_left_mem hz hm)
    simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hk
    cases hk
  obtain ⟨l₃, H₃, hl₃'⟩ := hrounds_of_comp_of (oneShot_splitH 0) hpair hl₃
  rw [hrounds_splitH0_inv H₃] at hl₃'
  have hl₄ := twos_of_pair_inr hl₃'
  -- the core node
  have hY : ∀ t ∈ ((modSem P).sem c.mod).comp
      (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length)), NoInl t :=
    noInl_comp (fun s _ => noInl_sigN0 s)
  have hl₅ := twos_of_comp_noInl hY hl₄
  obtain ⟨l₄, H₄, hl₆⟩ := hrounds_of_comp (oneShot_widenH _) (fun s _ => noInl_sigN0 s) hl₅
  -- `modSem` and `core3Sem`
  rw [modSem_sem hI] at hl₆
  have hZ : ∀ t ∈ (I.strategy P I.store).comp (Strategy.ofHandler (exportH (instNum hI))),
      NoInl t := noInl_comp (fun s _ => noInl_inst hI.2.1 s)
  have hl₇ := twos_of_comp_noInl hZ hl₆
  obtain ⟨l₅, H₅, hl₈⟩ := hrounds_of_comp (oneShot_exportH _) (fun s _ => noInl_inst hI.2.1 s) hl₇
  obtain ⟨q, hq⟩ := Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mp hl₈
  obtain ⟨s', hA⟩ := acts_of_path l₅ hq
  exact specRounds_of_chain hc hI _ l₂ l₄ l₅ I.store s' H₂ H₄ H₅ hA

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
