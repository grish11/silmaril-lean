module

public import Silmaril.Wasm.Component.Reference.LinkedSessionObs.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.Main
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Main
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Linked
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.IR
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.WitnessRun
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# The session triple of a linked component: rounds and determinism

* the triple has no plain traps, no pending calls and no productive streams;
* `round_det`: at the deterministic profiles one `Linked2.SessSpec` round is a function of the
  stores and the call: the importer's Proponent moves are unique (`strategy_deterministic`), the
  exporter's answers to the import calls are unique (`retAt_det`, `trapAt_det`,
  `retAt_not_trapAt`, through `result_unique`), so the core import calls, their answers, the
  outcome and both end stores agree (`impRel_det`, `calls_det`);
* `storeDet_compTripleS`: hence the triple is store-deterministic;
* `spec_of_roundsL`, `rounds_of_specL`: its completed rounds from a pair of stores are the
  `Linked2.SessSpec` sessions of their typed calls, the untyped questions trapping at once
  (`ShapedL`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet roundsMoves roundMoves)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionStrat
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {l : Linked2} {Ie Ii : SInst}

/-! ## The triple -/

theorem mem_compFin_none {s : Store Nat × Store Nat} {q : Nat × Payload} (h : l.typedQ q = none)
    {x : CallBeh (sigN 0) (Store Nat × Store Nat) (Payload ⊕ PUnit)} :
    x ∈ Linked2.compFin P l Ie Ii s q ↔ x = ([], .ret (.inr PUnit.unit) s) := by
  simp only [Linked2.compFin, h, Set.mem_singleton_iff]

theorem mem_compFin_some {s : Store Nat × Store Nat} {q : Nat × Payload}
    {j : Fin l.imp.exports.length} {vs : List IVal} (h : l.typedQ q = some (j, vs))
    {x : CallBeh (sigN 0) (Store Nat × Store Nat) (Payload ⊕ PUnit)} :
    x ∈ Linked2.compFin P l Ie Ii s q ↔ x.1 = [] ∧
      ((∃ (o : Option (List IVal)) (π' u' : Store Nat),
          Linked2.SessSpec P l Ie Ii s.2 s.1 [(j, vs)] [o] u' π' ∧
            x.2 = .ret (outAns o) (π', u')) ∨
        (Linked2.RoundDiv P l Ie Ii s.2 s.1 j vs ∧ x.2 = .div)) := by
  simp only [Linked2.compFin, h]
  rfl

theorem noPlainTrap_compTripleS : StratSession.NoPlainTrap (Linked2.compTripleS P l Ie Ii) := by
  intro s q c hm
  cases hq : l.typedQ q with
  | none => cases (mem_compFin_none hq).mp hm
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    obtain ⟨-, ⟨_, _, _, _, he⟩ | ⟨_, he⟩⟩ := (mem_compFin_some hq).mp hm <;> cases he

theorem satP_compTripleS (s : Store Nat × Store Nat) (q : Nat × Payload) :
    satP (Linked2.compTripleS P l Ie Ii) s q = ∅ := by
  ext x
  exact x.2.1.elim0

/-! ## Linked sessions -/

theorem sessSpec_cons_iff {u π u' π' : Store Nat} {q : Fin l.imp.exports.length × List IVal}
    {cs : List (Fin l.imp.exports.length × List IVal)} {o : Option (List IVal)}
    {os : List (Option (List IVal))} :
    Linked2.SessSpec P l Ie Ii u π (q :: cs) (o :: os) u' π' ↔
      ∃ u₁ π₁, Linked2.SessSpec P l Ie Ii u π [q] [o] u₁ π₁ ∧
        Linked2.SessSpec P l Ie Ii u₁ π₁ cs os u' π' := by
  constructor
  · intro h
    cases h with
    | round d hok hp he hans hr => exact ⟨_, _, .round d hok hp he hans (.nil _ _), hr⟩
  · rintro ⟨u₁, π₁, h₁, h₂⟩
    cases h₁ with
    | round d hok hp he hans hr =>
      cases hr
      exact .round d hok hp he hans h₂

theorem sessSpec_append :
    ∀ {u π u'' π'' : Store Nat} {c₁ c₂ : List (Fin l.imp.exports.length × List IVal)}
      {o₁ o₂ : List (Option (List IVal))}, c₁.length = o₁.length →
      (Linked2.SessSpec P l Ie Ii u π (c₁ ++ c₂) (o₁ ++ o₂) u'' π'' ↔
        ∃ u' π', Linked2.SessSpec P l Ie Ii u π c₁ o₁ u' π' ∧
          Linked2.SessSpec P l Ie Ii u' π' c₂ o₂ u'' π'')
  | u, π, _, _, [], _, [], _, _ =>
    ⟨fun h => ⟨u, π, .nil u π, h⟩, fun ⟨_, _, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | _, _, _, _, [], _, _ :: _, _, h => by cases h
  | _, _, _, _, _ :: _, _, [], _, h => by cases h
  | _, _, _, _, q :: c₁, c₂, o :: o₁, o₂, h => by
    rw [List.cons_append, List.cons_append, sessSpec_cons_iff]
    constructor
    · rintro ⟨u₁, π₁, h₁, h₂⟩
      obtain ⟨u', π', h₃, h₄⟩ := (sessSpec_append (by simpa using h)).mp h₂
      exact ⟨u', π', sessSpec_cons_iff.mpr ⟨u₁, π₁, h₁, h₃⟩, h₄⟩
    · rintro ⟨u', π', h₁, h₂⟩
      obtain ⟨u₁, π₁, h₃, h₄⟩ := sessSpec_cons_iff.mp h₁
      exact ⟨u₁, π₁, h₃, (sessSpec_append (by simpa using h)).mpr ⟨u', π', h₄, h₂⟩⟩

theorem sessSpec_single {u π u' π' : Store Nat} {j : Fin l.imp.exports.length} {vs : List IVal}
    {o : Option (List IVal)} (h : Linked2.SessSpec P l Ie Ii u π [(j, vs)] [o] u' π') :
    ∃ d : Linked2.SessRound l Ii, d.j = j ∧ d.vs = vs ∧ d.Ok ∧
      Ii.Path P (.idle u) d.instMoves (.idle u') ∧
      Linked2.ExpRunT P l Ie π d.dss.flatten π' ∧ d.ans = o.map .vals := by
  generalize hc : [(j, vs)] = cs at h
  cases h with
  | round d hok hp he hans hr =>
    cases hr
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hc
    exact ⟨d, hc.1.symm, hc.2.symm, hok, hp, he, hans⟩

/-! ## Determinism of a round -/

section Det

variable {o : GrowOracle}

theorem retAt_det {c : Simple} {I : SInst} {x : SimpleExport} {vs ws ws' : List IVal}
    {s s₁ s₂ : Store Nat} (h : RetAt (profile o) c I x vs s ws s₁)
    (h' : RetAt (profile o) c I x vs s ws' s₂) : ws = ws' ∧ s₁ = s₂ := by
  obtain ⟨_, cvs, ys, run, fin, hys, hws⟩ := h.run
  obtain ⟨_, cvs', ys', run', fin', hys', hws'⟩ := h'.run
  obtain ⟨rfl, rfl, he⟩ := result_unique run fin run' fin'
  cases he
  rw [hys] at hys'
  cases hys'
  rw [hws] at hws'
  cases hws'
  exact ⟨rfl, rfl⟩

theorem trapAt_det {c : Simple} {I : SInst} {x : SimpleExport} {vs : List IVal}
    {s s₁ s₂ : Store Nat} (h : TrapAt (profile o) c I x vs s s₁)
    (h' : TrapAt (profile o) c I x vs s s₂) : s₁ = s₂ := by
  obtain ⟨_, _, run, fin, -⟩ := h.run
  obtain ⟨_, _, run', fin', -⟩ := h'.run
  exact (result_unique run fin run' fin').1.symm

theorem retAt_not_trapAt {c : Simple} {I : SInst} {x : SimpleExport} {vs ws : List IVal}
    {s s₁ s₂ : Store Nat} (h : RetAt (profile o) c I x vs s ws s₁)
    (h' : TrapAt (profile o) c I x vs s s₂) : False := by
  obtain ⟨_, cvs, ys, run, fin, hys, hws⟩ := h.run
  obtain ⟨_, res, run', fin', hl⟩ := h'.run
  obtain ⟨rfl, rfl, rfl⟩ := result_unique run fin run' fin'
  simp [coreRes, hys, liftOutcome, hws] at hl

/-- **The exporter answers an import call uniquely.** -/
theorem expRunT_one_det {π πa πb : Store Nat} {k : Fin l.imp.imports.length} {ws : List IVal}
    {R R' : Option Payload}
    (r : Linked2.ExpRunT (profile o) l Ie π [⟨(k, .vals ws), R⟩] πa)
    (r' : Linked2.ExpRunT (profile o) l Ie π [⟨(k, .vals ws), R'⟩] πb) : R = R' ∧ πa = πb := by
  cases r with
  | ret w hw hret hr =>
    cases hr
    cases r' with
    | ret w' hw' hret' hr' =>
      cases hr'
      obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      obtain ⟨rfl, rfl⟩ := retAt_det hret hret'
      exact ⟨rfl, rfl⟩
    | trap w' hw' htrap' hr' =>
      obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      exact (retAt_not_trapAt hret htrap').elim
  | trap w hw htrap hr =>
    cases hr
    cases r' with
    | ret w' hw' hret' hr' =>
      obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      exact (retAt_not_trapAt hret' htrap).elim
    | trap w' hw' htrap' hr' =>
      cases hr'
      obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      exact ⟨rfl, trapAt_det htrap htrap'⟩

/-- **One core import call, answered by the exporter, is determined by its question.** -/
theorem impRel_det {c c' : Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds ds' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)} {π πa πb : Store Nat}
    (he : c.1 = c'.1) (h : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds)
    (h' : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c' ds')
    (r : Linked2.ExpRunT (profile o) l Ie π ds πa)
    (r' : Linked2.ExpRunT (profile o) l Ie π ds' πb) : c = c' ∧ ds = ds' ∧ πa = πb := by
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
    obtain ⟨rfl, rfl⟩ := expRunT_one_det r r'
    subst hA hA'
    exact ⟨rfl, rfl, rfl⟩

theorem mem_ask_of {u : Store Nat} {pre : List (Move Ii.E Ii.F)} {x : Σ e : Ii.E.Op, Ii.E.Ar e}
    {xs : List (Σ e : Ii.E.Op, Ii.E.Ar e)} {tail : List (Move Ii.E Ii.F)}
    (h : pre ++ (Silmaril.Wasm.Component.Reference.callMoves (x :: xs) ++ tail) ∈
      Ii.strategy (profile o) u) :
    pre ++ [.inl (.ask x.1)] ∈ Ii.strategy (profile o) u :=
  (Ii.strategy (profile o) u).of_prefix h
    ⟨.inl (.ans x.1 x.2) :: (Silmaril.Wasm.Component.Reference.callMoves xs ++ tail), by
      obtain ⟨e, n⟩ := x
      simp [Silmaril.Wasm.Component.Reference.callMoves]⟩

/-- **The importer's import calls and answer are determined**, given the exporter's answers. -/
theorem calls_det {u : Store Nat} {f : Ii.F.Op} :
    ∀ (cs cs' : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss dss' : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (pre : List (Move Ii.E Ii.F)) (w w' : Ii.F.Ar f) (π π₁ π₂ : Store Nat),
      pre ++ (Silmaril.Wasm.Component.Reference.callMoves cs ++ [.inr (.ans f w)]) ∈
        Ii.strategy (profile o) u →
      pre ++ (Silmaril.Wasm.Component.Reference.callMoves cs' ++ [.inr (.ans f w')]) ∈
        Ii.strategy (profile o) u →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs' dss' →
      Linked2.ExpRunT (profile o) l Ie π dss.flatten π₁ →
      Linked2.ExpRunT (profile o) l Ie π dss'.flatten π₂ →
      cs = cs' ∧ w = w' ∧ π₁ = π₂
  | [], [], _, _, pre, w, w', π, π₁, π₂, h, h', hr, hr', r, r' => by
    cases hr
    cases hr'
    cases r
    cases r'
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic h h' trivial
    simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at e
    exact ⟨rfl, e, rfl⟩
  | [], c' :: cs', _, _, pre, w, w', π, π₁, π₂, h, h', _, _, _, _ => by
    exfalso
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic h (mem_ask_of h') trivial
    cases e
  | c :: cs, [], _, _, pre, w, w', π, π₁, π₂, h, h', _, _, _, _ => by
    exfalso
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic (mem_ask_of h) h' trivial
    cases e
  | c :: cs, c' :: cs', dss, dss', pre, w, w', π, π₁, π₂, h, h', hr, hr', r, r' => by
    obtain ⟨ds, dss₁, hd, hr₁, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨ds', dss₁', hd', hr₁', rfl⟩ := List.forall₂_cons_left_iff.mp hr'
    rw [List.flatten_cons] at r r'
    obtain ⟨πa, ra, rb⟩ := LinkedSessionAdeq.expRunT_split _ _ r
    obtain ⟨πb, ra', rb'⟩ := LinkedSessionAdeq.expRunT_split _ _ r'
    have hm : ∀ (x : Σ e : Ii.E.Op, Ii.E.Ar e) (xs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
        (v : Ii.F.Ar f),
        pre ++ (Silmaril.Wasm.Component.Reference.callMoves (x :: xs) ++ [.inr (.ans f v)]) =
          (pre ++ [.inl (.ask x.1), .inl (.ans x.1 x.2)]) ++
            (Silmaril.Wasm.Component.Reference.callMoves xs ++ [.inr (.ans f v)]) := by
      intro x xs v
      obtain ⟨e, n⟩ := x
      simp [Silmaril.Wasm.Component.Reference.callMoves]
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic (mem_ask_of h)
      (mem_ask_of h') trivial
    simp only [Sum.inl.injEq, Ev.ask.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := impRel_det e hd hd' ra ra'
    rw [hm] at h h'
    obtain ⟨rfl, rfl, rfl⟩ := calls_det cs cs' dss₁ dss₁' _ w w' πa π₁ π₂ h h' hr₁ hr₁' rb rb'
    exact ⟨rfl, rfl, rfl⟩

theorem fOp_ext {f f' : Ii.F.Op} (h₁ : f.1.val = f'.1.val) (h₂ : f.2.1 = f'.2.1) : f = f' := by
  obtain ⟨⟨i, hi⟩, ⟨a, ha⟩⟩ := f
  obtain ⟨⟨i', hi'⟩, ⟨a', ha'⟩⟩ := f'
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- **A round of a linked session is a function of the stores and the call** (deterministic
profiles): the outcome and both end stores agree. -/
theorem round_det {u π u₁ π₁ u₂ π₂ : Store Nat} {j : Fin l.imp.exports.length} {vs : List IVal}
    {o₁ o₂ : Option (List IVal)}
    (h₁ : Linked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₁] u₁ π₁)
    (h₂ : Linked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₂] u₂ π₂) :
    o₁ = o₂ ∧ u₁ = u₂ ∧ π₁ = π₂ := by
  obtain ⟨⟨j₁, vs₁, f, cs, w, dss⟩, rfl, rfl, ⟨xs, hck, hf₁, hf₂, hrel⟩, hp, he, hans⟩ :=
    sessSpec_single h₁
  obtain ⟨⟨j₂, vs₂, f', cs', w', dss'⟩, hj, hv, ⟨xs', hck', hf₁', hf₂', hrel'⟩, hp', he', hans'⟩ :=
    sessSpec_single h₂
  simp only at hj hv hck hf₁ hf₂ hrel hp he hans hck' hf₁' hf₂' hrel' hp' he' hans'
  subst hj hv
  rw [hck] at hck'
  cases hck'
  obtain rfl : f = f' := fOp_ext (hf₁.trans hf₁'.symm) (hf₂.trans hf₂'.symm)
  have hm : ∀ (c : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (v : Ii.F.Ar f),
      (.inr (.ask f) :: Silmaril.Wasm.Component.Reference.callMoves c ++ [.inr (.ans f v)] :
        List (Move Ii.E Ii.F)) =
        [.inr (.ask f)] ++ (Silmaril.Wasm.Component.Reference.callMoves c ++ [.inr (.ans f v)]) :=
    fun _ _ => rfl
  have hs := (Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff).mpr ⟨_, hp⟩
  have hs' := (Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff).mpr ⟨_, hp'⟩
  simp only [Linked2.SessRound.instMoves] at hs hs' hp hp'
  rw [hm] at hs hs'
  obtain ⟨rfl, rfl, rfl⟩ := calls_det cs cs' dss dss' _ w w' π π₁ π₂ hs hs' hrel hrel' he he'
  refine ⟨?_, Silmaril.Wasm.Game.ScalarInstance.activation_functional hp hp', rfl⟩
  simp only [Linked2.SessRound.ans] at hans hans'
  rw [hans] at hans'
  exact Option.map_injective (fun _ _ h => Payload.vals.inj h) hans'

/-- **Store determinism** of the linked triple at the deterministic profiles. -/
theorem storeDet_compTripleS : StoreDet (Linked2.compTripleS (profile o) l Ie Ii) := by
  intro s q c b s₁ s₂ h₁ h₂
  cases hq : l.typedQ q with
  | none =>
    have e₁ := (mem_compFin_none hq).mp h₁
    have e₂ := (mem_compFin_none hq).mp h₂
    simp only [Prod.mk.injEq, End.ret.injEq] at e₁ e₂
    rw [e₁.2.2, e₂.2.2]
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    obtain ⟨-, ⟨o₁, π₁, u₁, hs₁, he₁⟩ | ⟨-, he₁⟩⟩ := (mem_compFin_some hq).mp h₁ <;>
      obtain ⟨-, ⟨o₂, π₂, u₂, hs₂, he₂⟩ | ⟨-, he₂⟩⟩ := (mem_compFin_some hq).mp h₂ <;>
      simp only [End.ret.injEq, reduceCtorEq] at he₁ he₂
    obtain ⟨-, rfl⟩ := he₁
    obtain ⟨-, rfl⟩ := he₂
    obtain ⟨-, rfl, rfl⟩ := round_det hs₁ hs₂
    rfl

end Det

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs
