module

public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Main
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Triple

/-!
# Deterministic exporters

* `run_functional`, `adeqIC_of_det`: the sessions of a deterministic exporter are determined by
  their rounds, so the runs of the finite prefixes of an infinite play (`ExpSpec.Adeq.bwd`)
  extend one another: `ExpSpec.AdeqIC`;
* `simple_det`: a simple component at `profile o` (`LinkedSessionObs.retAt_det`, `trapAt_det`,
  `retAt_not_trapAt`);
* `toExp_det`: a linked component at `profile o`, for a deterministic exporter: the importer's
  Proponent moves are unique (`Trans.player_unique`), the exporter answers its import calls
  uniquely (`impRel_detG`), so the core import calls, the answer and both end states agree
  (`calls_detG`; `LinkedSessionObs.round_det` over the interface);
* `chain_det`: chains, by induction.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq (streamTake_snoc)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Deterministic exporters serve infinite plays along one run -/

section Run

variable {P : Profile} {e : ExpSpec}

theorem run_functional (hd : e.Det P) {s s₁ s₂ : e.St} {L : List URound}
    (h₁ : e.Run P s L s₁) (h₂ : e.Run P s L s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | nil => cases h₂; rfl
  | cons hs _ ih =>
    cases h₂ with
    | cons hs' h₂' =>
      obtain ⟨-, rfl⟩ := hd hs hs'
      exact ih h₂'

theorem typed_stream {L₀ : List URound} {T : ℕ → List URound} (h₀ : ∀ r ∈ L₀, e.Typed r)
    (hT : ∀ k, ∀ r ∈ T k, e.Typed r) (n : ℕ) :
    ∀ r ∈ L₀ ++ (streamTake T n).flatten, e.Typed r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₀ r hr
  · obtain ⟨l, hl, hr⟩ := List.mem_flatten.mp hr
    simp only [streamTake, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact hT i r hr

/-- **A deterministic exporter meets `AdeqIC`**: the sessions of the prefixes, given by `bwd`,
extend one another. -/
theorem adeqIC_of_det (he : e.Adeq P) (hd : e.Det P) : e.AdeqIC P := by
  intro L₀ T h₀ hT h
  have hrun : ∀ n, ∃ s, e.Run P e.init (L₀ ++ (streamTake T n).flatten) s := fun n =>
    he.bwd _ (typed_stream h₀ hT n) (h n)
  choose S hS using hrun
  refine ⟨S, ?_, fun k => ?_⟩
  · have h₀' := hS 0
    simpa [streamTake] using h₀'
  · have h₁ := hS (k + 1)
    rw [streamTake_snoc, List.flatten_append, List.flatten_singleton, ← List.append_assoc]
      at h₁
    obtain ⟨π, ha, hb⟩ := run_split _ _ h₁
    obtain rfl := run_functional hd ha (hS k)
    exact hb

end Run

/-! ## A simple exporter -/

/-- **A simple exporter is deterministic** at `profile o`. -/
theorem simple_det (o : GrowOracle) (c : Simple) (I : SInst) :
    (Simple.expSpec c I).Det (profile o) := by
  intro s s₁ s₂ q a₁ a₂ h₁ h₂
  cases h₁ with
  | ret hj hr =>
    cases h₂ with
    | ret hj' hr' =>
      obtain ⟨rfl, rfl⟩ := LinkedSessionObs.retAt_det hr hr'
      exact ⟨rfl, rfl⟩
    | trap hj' ht' => exact (LinkedSessionObs.retAt_not_trapAt hr ht').elim
  | trap hj ht =>
    cases h₂ with
    | ret hj' hr' => exact (LinkedSessionObs.retAt_not_trapAt hr' ht).elim
    | trap hj' ht' => exact ⟨rfl, LinkedSessionObs.trapAt_det ht ht'⟩

/-! ## A linked component -/

section Linked

variable {o : GrowOracle} {g : LinkedG} {Ii : SInst}

/-- **The exporter answers one wired import call uniquely.** -/
theorem expRunG_one_det (hd : g.exp.Det (profile o)) {π πa πb : g.exp.St}
    {k : Fin g.imp.imports.length} {p : Payload} {R R' : Option Payload}
    (r : LinkedG.ExpRun (profile o) g π [⟨(k, p), R⟩] πa)
    (r' : LinkedG.ExpRun (profile o) g π [⟨(k, p), R'⟩] πb) : R = R' ∧ πa = πb := by
  cases r with
  | step w hw hs hr =>
    cases hr
    cases r' with
    | step w' hw' hs' hr' =>
      cases hr'
      obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      exact hd hs hs'

/-- **One core import call, answered by the exporter, is determined by its question.** -/
theorem impRel_detG (hd : g.exp.Det (profile o)) {c c' : Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds ds' : List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload)} {π πa πb : g.exp.St}
    (he : c.1 = c'.1) (h : Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii c ds) (h' : Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii c' ds')
    (r : LinkedG.ExpRun (profile o) g π ds πa) (r' : LinkedG.ExpRun (profile o) g π ds' πb) :
    c = c' ∧ ds = ds' ∧ πa = πb := by
  obtain ⟨e, n⟩ := c
  obtain ⟨e', n'⟩ := c'
  simp only at he
  subst he
  obtain ⟨nm, ft, A, hi, hA, hm⟩ := h
  obtain ⟨nm', ft', A', hi', hA', hm'⟩ := h'
  rw [hi] at hi'
  cases hi'
  simp only at hA hA' hm hm'
  cases hl : liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
  | none =>
    rw [hl] at hm hm'
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨rfl, rfl⟩ := hm'
    cases r
    cases r'
    subst hA hA'
    exact ⟨rfl, rfl, rfl⟩
  | some ws =>
    rw [hl] at hm hm'
    obtain ⟨hk, R, rfl, rfl⟩ := hm
    obtain ⟨hk', R', rfl, rfl⟩ := hm'
    obtain ⟨rfl, rfl⟩ := expRunG_one_det hd r r'
    subst hA hA'
    exact ⟨rfl, rfl, rfl⟩

/-- **The importer's import calls and answer are determined**, given a deterministic exporter:
from one hidden state, two runs of core import calls served by the exporter from one state,
then an answer, agree. -/
theorem calls_detG (hd : g.exp.Det (profile o)) {f : Ii.F.Op} :
    ∀ {cs cs' : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
      {dss dss' : List (List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))}
      {q z z' : Ii.HState} {w w' : Ii.F.Ar f} {π π₁ π₂ : g.exp.St},
      Ii.Path (profile o) q (callMoves cs ++ [.inr (.ans f w)]) z →
      Ii.Path (profile o) q (callMoves cs' ++ [.inr (.ans f w')]) z' →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii) cs dss → List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii) cs' dss' →
      LinkedG.ExpRun (profile o) g π dss.flatten π₁ →
      LinkedG.ExpRun (profile o) g π dss'.flatten π₂ →
      cs = cs' ∧ dss = dss' ∧ w = w' ∧ z = z' ∧ π₁ = π₂
  | [], [], _, _, _, _, _, _, _, _, _, _, hp, hp', .nil, .nil, r, r' => by
    cases r
    cases r'
    cases hp with
    | cons t h =>
      cases hp' with
      | cons t' h' =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t t' (by simp [Move.IsP])
        simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at e
        subst e
        obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t t'
        cases h
        cases h'
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | [], ⟨m', n'⟩ :: cs', _, _, _, _, _, _, _, _, _, _, hp, hp', _, _, _, _ => by
    exfalso
    cases hp with
    | cons t _ =>
      cases hp' with
      | cons t' _ =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t t' (by simp [Move.IsP])
        cases e
  | ⟨m, n⟩ :: cs, [], _, _, _, _, _, _, _, _, _, _, hp, hp', _, _, _, _ => by
    exfalso
    cases hp with
    | cons t _ =>
      cases hp' with
      | cons t' _ =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t t' (by simp [Move.IsP])
        cases e
  | ⟨m, n⟩ :: cs, ⟨m', n'⟩ :: cs', _, _, _, _, _, _, _, _, _, _, hp, hp', .cons hc F,
      .cons hc' F', r, r' => by
    rw [List.flatten_cons] at r r'
    obtain ⟨πa, ra, rb⟩ := expRunG_split _ _ r
    obtain ⟨πb, ra', rb'⟩ := expRunG_split _ _ r'
    cases hp with
    | cons t₁ hp₁ =>
      cases hp' with
      | cons t₁' hp₁' =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₁ t₁'
          (by simp [Move.IsP])
        simp only [Sum.inl.injEq, Ev.ask.injEq] at e
        subst e
        obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₁ t₁'
        obtain ⟨hc₁, rfl, rfl⟩ :=
          impRel_detG (c := ⟨m, n⟩) (c' := ⟨m, n'⟩) hd rfl hc hc' ra ra'
        obtain rfl : n = n' := eq_of_heq (Sigma.mk.inj hc₁).2
        cases hp₁ with
        | cons t₂ hp₂ =>
          cases hp₁' with
          | cons t₂' hp₂' =>
            obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₂ t₂'
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := calls_detG hd hp₂ hp₂' F F' rb rb'
            exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A linked component with a deterministic exporter is deterministic** at `profile o`. -/
theorem toExp_det (hd : g.exp.Det (profile o)) : (g.toExp Ii).Det (profile o) := by
  intro s s₁ s₂ q a₁ a₂ h₁ h₂
  obtain ⟨⟨j, vs, f, cs, w, dss⟩, ⟨xs, hck, hf₁, hf₂, hrel⟩, hp, he, hq⟩ := h₁
  obtain ⟨⟨j', vs', f', cs', w', dss'⟩, ⟨xs', hck', hf₁', hf₂', hrel'⟩, hp', he', hq'⟩ := h₂
  obtain ⟨hq₁, ha₁⟩ := Sigma.mk.inj hq
  obtain ⟨hq₂, ha₂⟩ := Sigma.mk.inj hq'
  have hjv : ((j.val, Payload.vals vs) : sigU.Op) = (j'.val, .vals vs') := hq₁.symm.trans hq₂
  simp only [Prod.mk.injEq, Payload.vals.injEq] at hjv
  obtain ⟨hj, rfl⟩ := hjv
  obtain rfl : j = j' := Fin.ext hj
  simp only at hck hf₁ hf₂ hrel hp he hck' hf₁' hf₂' hrel' hp' he'
  rw [hck] at hck'
  cases hck'
  obtain rfl : f = f' := LinkedSessionObs.fOp_ext (hf₁.trans hf₁'.symm) (hf₂.trans hf₂'.symm)
  simp only [LinkedG.SessRound.instMoves] at hp hp'
  cases hp with
  | cons t hp₁ =>
    cases hp' with
    | cons t' hp₁' =>
      obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t t'
      obtain ⟨rfl, rfl, rfl, hz, hπ⟩ := calls_detG hd hp₁ hp₁' hrel hrel' he he'
      refine ⟨(eq_of_heq ha₁).trans (eq_of_heq ha₂).symm, Prod.ext ?_ hπ⟩
      injection hz

end Linked

/-- **Chains on a deterministic exporter are deterministic** at `profile o`. -/
theorem chain_det (o : GrowOracle) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst), e.Det (profile o) →
      (chainExp e bs Is).Det (profile o)
  | _, [], _, h => h
  | _, (_, _) :: _, [], h => h
  | _, (_, _) :: bs, _ :: Is, h => chain_det o _ bs Is (toExp_det h)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter
