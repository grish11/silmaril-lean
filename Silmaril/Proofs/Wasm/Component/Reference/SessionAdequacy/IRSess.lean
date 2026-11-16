module

public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Main

/-!
# The plays of a simple component's IR as specification sessions

`SessRounds P c I s Lu s'`: the rounds `Lu` (at the untyped interface `sigU`) read as a
session of the specification from the store `s` to `s'`. A round is

* an ill-typed question (out of the typed export calls: a payload of the wrong kind or values
  of the wrong types) answered by a trap, the store unchanged (`bad`);
* a returned call (`RetAt`) answered by its results (`ret`);
* a trapped call (`TrapAt`) answered by a trap, the next round starting at the store the trap
  left (`trap`): the IR instance keeps its store after a trap.

`sessRounds_of_den`: the complete rounds of every play of `c.toComp.den (modSem P)` are such a
session from the instance's store; `den_of_sessRounds`: conversely, every such session is the
complete rounds of a play. The read-back is #669's (`specRounds_of_den`), recording in
addition the run of a trapped call (`RoundSpecT`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile}

/-! ## Rounds read with the store of a trap -/

/-- **A round read as the specification at the store `s`**, ending at the store `s₁`: a trap at
once (an ill-typed call or a payload of the wrong kind), the store unchanged; or a typed call
whose lowered values run the core export host-free from `s` to a result `res` at `s₁`,
answered by the lift of `res`. -/
def RoundSpecT (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) (s : Store Nat) :
    Round sigU → Store Nat → Prop
  | ⟨(j, p), A⟩, s₁ =>
    (A = none ∧ s₁ = s ∧ ∀ (hj : j < c.exports.length) (vs : List IVal),
      p = .vals vs → checkLower c.exports[j].ty.params vs = none) ∨
    ∃ (hj : j < c.exports.length) (vs : List IVal) (t' : STh) (res : Result),
      p = .vals vs ∧ ValTy.checkList c.exports[j].ty.params vs = true ∧
      Silmaril.Wasm.Game.Reach P (s, Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
        (lowerArgs c.exports[j].ty.params vs)) (s₁, t') ∧
      Silmaril.Wasm.Game.ResultAt s₁ t' res ∧
      A = ((coreRes res).map Payload.flat).bind (Adapter.up (.lift c.exports[j].ty))

/-- Rounds read as the specification, threading the store. -/
inductive SpecRoundsT (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (Round sigU) → Prop where
  | nil (s : Store Nat) : SpecRoundsT P c I s []
  | cons {s s₁ : Store Nat} {x : Round sigU} {l : List (Round sigU)} :
      RoundSpecT P c I s x s₁ → SpecRoundsT P c I s₁ l → SpecRoundsT P c I s (x :: l)

/-- **The handler chain read as the specification** (`specRounds_of_chain`, with the runs). -/
theorem specRoundsT_of_chain {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ (l l₂ : List (Round sigU)) (l₄ : List (Round (CoreIface.sig (CoreModule.exports c.mod))))
      (l₅ : List (Round I.F)) (s s' : Store Nat),
      HRounds (exportsH c.mod.exports.length c.toComp.exports) l l₂ →
      HRounds (widenH (CoreModule.exports c.mod).length) l₂ l₄ →
      HRounds (exportH (instNum hI)) l₄ l₅ → Acts P I s l₅ s' → SpecRoundsT P c I s l
  | [], _, _, _, s, _, _, _, _, _ => .nil s
  | ⟨(j, p), A⟩ :: l, l₂, l₄, l₅, s, s', H₂, H₄, H₅, hA => by
    rcases hrounds_cons_inv H₂ with ⟨hq, H₂'⟩ | ⟨q₂, k₂, a₂, l₂', rfl, hq, hk, H₂'⟩
    · rcases exportsH_shape hc (j, p) with ⟨he, hn⟩ | ⟨hj, vs, xs, hp, hl, he⟩
      · rw [he] at hq
        cases hq
        exact .cons (.inl ⟨rfl, rfl, hn⟩)
          (specRoundsT_of_chain hc hI l l₂ l₄ l₅ s s' H₂' H₄ H₅ hA)
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
        have hrest := specRoundsT_of_chain hc hI l l₂' l₄' l₅' s₁ s' H₂' H₄' H₅' hA'
        obtain ⟨hck, rfl⟩ := checkLower_eq hl
        refine .cons (.inr ⟨hj, vs, t, res, hp, hck, run, final, ?_⟩) hrest
        rw [answerPayload_of_ofResult? answer]
        cases res <;> rfl

/-- **Complete rounds of the IR denotation are specification rounds** from the instance's
store (`specRounds_of_den`, with the runs). -/
theorem specRoundsT_of_den {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {L : List (Round (sigN c.toComp.exports.length))}
    (h : twos L ∈ c.toComp.den (modSem P)) : SpecRoundsT P c I I.store (L.map Round.forget) := by
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
  exact specRoundsT_of_chain hc hI _ l₂ l₄ l₅ I.store s' H₂ H₄ H₅ hA

/-! ## Sessions of rounds -/

/-- **Rounds read as a session of the specification** from the store `s` to `s'`. -/
inductive SessRounds (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (Round sigU) → Store Nat → Prop where
  | nil (s : Store Nat) : SessRounds P c I s [] s
  | bad {s s' : Store Nat} {j : Nat} {p : Payload} {L : List (Round sigU)} :
      j < c.exports.length →
      (∀ (hj : j < c.exports.length) (vs : List IVal), p = .vals vs →
        ValTy.checkList c.exports[j].ty.params vs = false) →
      SessRounds P c I s L s' → SessRounds P c I s (⟨(j, p), none⟩ :: L) s'
  | ret {s s₁ s' : Store Nat} {j : Nat} {vs ws : List IVal} {L : List (Round sigU)}
      (hj : j < c.exports.length) :
      RetAt P c I c.exports[j] vs s ws s₁ → SessRounds P c I s₁ L s' →
      SessRounds P c I s (⟨(j, .vals vs), some (.vals ws)⟩ :: L) s'
  | trap {s s₁ s' : Store Nat} {j : Nat} {vs : List IVal} {L : List (Round sigU)}
      (hj : j < c.exports.length) :
      TrapAt P c I c.exports[j] vs s s₁ → SessRounds P c I s₁ L s' →
      SessRounds P c I s (⟨(j, .vals vs), none⟩ :: L) s'

theorem checkList_false_of {ts : List ValTy} {vs : List IVal} (h : checkLower ts vs = none) :
    ValTy.checkList ts vs = false := by
  cases hc : ValTy.checkList ts vs with
  | false => rfl
  | true => rw [checkLower_of_check hc] at h; cases h

theorem checkLower_none_of {ts : List ValTy} {vs : List IVal} (h : ValTy.checkList ts vs = false) :
    checkLower ts vs = none := by
  unfold checkLower
  simp [h]

/-- A trapping lift outcome is the IR trap answer. -/
theorem up_none_of_traps {ft : FuncTy} {r : Option (List Flat)}
    (h : liftOutcome ft r = .traps) : (r.map Payload.flat).bind (Adapter.up (.lift ft)) = none := by
  have := obsAns_liftOutcome ft r
  rw [h] at this
  exact this

/-- The IR trap answer is a trapping lift outcome. -/
theorem traps_of_up_none {ft : FuncTy} {r : Option (List Flat)}
    (h : (r.map Payload.flat).bind (Adapter.up (.lift ft)) = none) : liftOutcome ft r = .traps := by
  have := obsAns_liftOutcome ft r
  rw [h] at this
  cases hb : liftOutcome ft r with
  | returns o =>
    rw [hb] at this
    cases o with
    | none => exact this.elim
    | some _ => obtain ⟨_, -, h'⟩ := this; cases h'
  | traps => rfl
  | deadlocks => rw [hb] at this; exact this.elim
  | diverges => rw [hb] at this; exact this.elim

/-- **Specification rounds are a session.** -/
theorem sessRounds_of_specRoundsT {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s : Store Nat} {Lu : List (Round sigU)}, SpecRoundsT P c I s Lu →
      (∀ x ∈ Lu, x.1.1 < c.exports.length) → ∃ s', SessRounds P c I s Lu s'
  | s, [], _, _ => ⟨s, .nil s⟩
  | s, ⟨(j, p), A⟩ :: Lu, .cons hr h, hlt => by
    have hlt' : ∀ x ∈ Lu, x.1.1 < c.exports.length := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    have hj₀ : j < c.exports.length := hlt _ List.mem_cons_self
    rcases hr with ⟨rfl, rfl, hn⟩ | ⟨hj, vs, t', res, rfl, hck, run, final, hA⟩
    · obtain ⟨s', h'⟩ := sessRounds_of_specRoundsT h hlt'
      exact ⟨s', .bad hj₀ (fun hj vs hp => checkList_false_of (hn hj vs hp)) h'⟩
    obtain ⟨s', h'⟩ := sessRounds_of_specRoundsT h hlt'
    cases A with
    | none =>
      exact ⟨s', .trap hj ⟨hck, t', res, run, final, traps_of_up_none hA.symm⟩ h'⟩
    | some a =>
      cases res with
      | values cvs =>
        cases hys : cvs.mapM toFlat? with
        | none => simp [coreRes, hys] at hA
        | some ys =>
          cases hws : liftArgs c.exports[j].ty.results ys with
          | none => simp [coreRes, hys, Adapter.up, hws] at hA
          | some ws =>
            have ha : a = .vals ws := by simpa [coreRes, hys, Adapter.up, hws] using hA
            subst ha
            exact ⟨s', .ret hj ⟨hck, t', cvs, ys, run, final, hys, hws⟩ h'⟩
      | trap => simp [coreRes] at hA
      | throw _ => simp [coreRes] at hA

/-- **The complete rounds of every play are a session** from the instance's store. -/
theorem sessRounds_of_den {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {L : List (Round (sigN c.toComp.exports.length))}
    (h : twos L ∈ c.toComp.den (modSem P)) :
    ∃ s', SessRounds P c I I.store (L.map Round.forget) s' :=
  sessRounds_of_specRoundsT (specRoundsT_of_den hc hI h) fun _ hx => forget_mem_lt hx

/-! ## Sessions are plays -/

/-- A trapped call is one complete activation of the instance and one round through the export
handlers, answered by a trap (`retAt_rounds` for traps). -/
theorem trapAt_rounds {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {j : Fin c.exports.length}
    {vs : List IVal} {s s' : Store Nat} (hw : I.WellFormed s)
    (h : TrapAt P c I c.exports[j] vs s s') :
    ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))),
      I.Activation P s (twos li) s' ∧ HRounds (exportH (instNum hI)) lc li ∧
      HRounds (exportsH c.mod.exports.length c.toComp.exports)
        [⟨(j.val, .vals vs), none⟩] (lc.map Round.forget) := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
      c.mod.exports[c.exports[j].core].2.params := by
    rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget]
    exact lowerList_types _ _ h.typed
  obtain ⟨t', res, run, final, htr⟩ := h.run
  have steps : Steps P Det.noHost (invoke s (I.addrs.getD c.exports[j].core 0)
      ((lowerArgs c.exports[j].ty.params vs).map ofFlat)) (t'.config s') :=
    internalP_steps (H := Nat) run
  obtain ⟨w, hw'⟩ := answer_at hI hw hk hxs steps (r := res) final
  have hpath : I.Activation P s (twos [⟨opAt hI hk hxs, w⟩]) s' :=
    .cons (.call s _) (.cons (.oret run final hw') (.nil _))
  have hpay : answerPayload w = (coreRes res).map .flat := by
    rw [answerPayload_of_ofResult? hw']
    cases res <;> rfl
  refine ⟨[⟨opAt hI hk hxs, w⟩],
    [⟨(⟨c.exports[j].core, hk⟩, .flat (lowerArgs c.exports[j].ty.params vs)), answerPayload w⟩],
    hpath, .call (h := exportH (instNum hI)) (exportH_round hI hk hxs) rfl .nil, ?_⟩
  exact exportsH_call c j.isLt vs hk (checkLower_of_check h.typed) _ _
    (by rw [hpay]; exact up_none_of_traps htr)

/-- **A session is activations of the instance** and rounds through the export handlers. -/
theorem sessRounds_rounds {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ {s s' : Store Nat} {Lu : List (Round sigU)}, SessRounds P c I s Lu s' → I.WellFormed s →
      ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))),
        I.Activation P s (twos li) s' ∧ HRounds (exportH (instNum hI)) lc li ∧
        HRounds (exportsH c.mod.exports.length c.toComp.exports) Lu (lc.map Round.forget)
  | _, _, _, .nil s, _ => ⟨[], [], .nil _, .nil, .nil⟩
  | _, _, _, .bad (j := j) (p := p) hj hn h, hw => by
    obtain ⟨li, lc, hact, H, X⟩ := sessRounds_rounds hc hI h hw
    refine ⟨li, lc, hact, H, .pure ?_ X⟩
    rcases exportsH_shape hc (j, p) with ⟨he, -⟩ | ⟨hj', vs, xs, hp, hl, -⟩
    · exact he
    · rw [checkLower_none_of (hn hj' vs hp)] at hl
      cases hl
  | _, _, _, .ret (j := j) hj hret h, hw => by
    have hw₁ := hret.wellFormed hI (hc.core _ (List.getElem_mem hj)) hw
    obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := retAt_rounds (j := ⟨j, hj⟩) hc hI hw hret
    obtain ⟨li, lc, hact, H, X⟩ := sessRounds_rounds hc hI h hw₁
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact path_append hact₁ hact
    · rw [List.map_append]
      exact X₁.append X
  | _, _, _, .trap (j := j) hj htrap h, hw => by
    have hw₁ := htrap.wellFormed hI (hc.core _ (List.getElem_mem hj)) hw
    obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := trapAt_rounds (j := ⟨j, hj⟩) hc hI hw htrap
    obtain ⟨li, lc, hact, H, X⟩ := sessRounds_rounds hc hI h hw₁
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact path_append hact₁ hact
    · rw [List.map_append]
      exact X₁.append X

theorem sessRounds_lt {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {Lu : List (Round sigU)}, SessRounds P c I s Lu s' →
      ∀ x ∈ Lu, x.1.1 < c.exports.length
  | _, _, _, .nil _, _, hx => nomatch hx
  | _, _, _, .bad hj _ h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hj
    · exact sessRounds_lt h x hx
  | _, _, _, .ret hj _ h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hj
    · exact sessRounds_lt h x hx
  | _, _, _, .trap hj _ h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hj
    · exact sessRounds_lt h x hx

/-- Rounds at `sigU` with small indices are rounds at `sigN n`. -/
theorem exists_forget {n : Nat} :
    ∀ (Lu : List (Round sigU)), (∀ x ∈ Lu, x.1.1 < n) →
      ∃ L : List (Round (sigN n)), L.map Round.forget = Lu
  | [], _ => ⟨[], rfl⟩
  | ⟨(j, p), A⟩ :: Lu, h => by
    obtain ⟨L, hL⟩ := exists_forget Lu fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨⟨(⟨j, h _ List.mem_cons_self⟩, p), A⟩ :: L, ?_⟩
    rw [List.map_cons, hL]
    rfl

/-- **A session from the instance's store is the complete rounds of a play.** -/
theorem den_of_sessRounds {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hc : c.Good) (hI : c.mod.IsInst I) {Lu : List (Round sigU)} {s' : Store Nat}
    (h : SessRounds P c I I.store Lu s') :
    ∃ L : List (Round (sigN c.toComp.exports.length)),
      twos L ∈ c.toComp.den (modSem P) ∧ L.map Round.forget = Lu := by
  obtain ⟨li, lc, hact, H, X⟩ := sessRounds_rounds hc hI h hI.1.choose_spec.ok
  have hinst : twos li ∈ I.strategy P I.store := by
    have h' := Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact (I.strategy P s').nil_mem
    rwa [List.append_nil] at h'
  have hsem : twos lc ∈ (modSem P).sem c.mod := sem_rounds hI H hinst
  have henv : twos (lc.map Round.forget) ∈ envS (modSem P) c := envS_rounds (modSem P) c hsem
  have hU : twos Lu ∈ c.toComp.denU (modSem P) := by
    rw [denU_toComp]
    exact twos_comp_ofHandler X henv
  obtain ⟨L, hL⟩ := exists_forget (n := c.toComp.exports.length) Lu fun x hx => by
    rw [toComp_length]
    exact sessRounds_lt h x hx
  refine ⟨L, den_rounds (modSem P) c.toComp ?_, hL⟩
  rw [hL]
  exact hU

end Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
