module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Triple
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Triple
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.ReadBack

/-!
# Determinism of a round with host calls

At the deterministic profiles one `HLinked2.SessSpec` round is a function of the stores, the call
and the host answers: two rounds from the same stores whose host calls agree on answers wherever
they agree on calls (`HostCompat`) make the same core import calls, the same component import
calls and end in the same outcome and stores (`round_detH`). In particular

* two rounds with the same host calls agree (store determinism of the triple);
* a round with host calls `c` and one with `c ++ [⟨m, none⟩]` cannot both exist;
* two rounds with `c ++ [⟨m, none⟩]` and `c ++ [⟨m', none⟩]` have `m = m'`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs
  (retAt_det trapAt_det retAt_not_trapAt mem_ask_of fOp_ext)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-- **Compatible host calls**: wherever two host-call lists ask the same call, they give the same
answer and continue compatibly. -/
def HostCompat {n : Nat} : List (Call (sigN n)) → List (Call (sigN n)) → Prop
  | x :: xs, y :: ys => x.1 = y.1 → x.2 = y.2 ∧ HostCompat xs ys
  | _, _ => True

theorem hostCompat_refl {n : Nat} : ∀ c : List (Call (sigN n)), HostCompat c c
  | [] => trivial
  | _ :: c => fun _ => ⟨rfl, hostCompat_refl c⟩

theorem hostCompat_append {n : Nat} :
    ∀ (c : List (Call (sigN n))) {X Y : List (Call (sigN n))}, HostCompat X Y →
      HostCompat (c ++ X) (c ++ Y)
  | [], _, _, h => h
  | _ :: c, _, _, h => fun _ => ⟨rfl, hostCompat_append c h⟩

theorem hostCompat_refuse {n : Nat} {m m' : (sigN n).Op} :
    HostCompat [(⟨m, none⟩ : Call (sigN n))] [⟨m', none⟩] :=
  fun _ => ⟨rfl, trivial⟩

variable {l : HLinked2} {Ie Ii : SInst} {o : GrowOracle}

theorem hostCalls_append (ds ds' : List (Call (sigN l.imp.imports.length))) :
    l.hostCalls (ds ++ ds') = l.hostCalls ds ++ l.hostCalls ds' :=
  List.filterMap_append

theorem wired_not_host {k : Nat} {w : Nat} (hw : l.wire[k]? = some w) (i : Fin l.host.length)
    (hi : k = l.wire.length + i.val) : False := by
  have : l.wire[k]? = none := List.getElem?_eq_none (by omega)
  rw [this] at hw
  cases hw

theorem hostCalls_one_wired {k : Fin l.imp.imports.length} {p : Payload} {R₀ : Option Payload}
    {w : Nat} (hw : l.wire[k.val]? = some w) :
    l.hostCalls [(⟨(k, p), R₀⟩ : Call (sigN l.imp.imports.length))] = [] := by
  have hlt : k.val < l.wire.length := by
    by_contra hc'
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hc')] at hw
  simp [HLinked2.hostCalls, HLinked2.hostCall?, Nat.not_le.2 hlt]

theorem hostCalls_one_host {k : Fin l.imp.imports.length} {p : Payload} {R₀ : Option Payload}
    (i : Fin l.host.length) (hi : k.val = l.wire.length + i.val) :
    l.hostCalls [(⟨(k, p), R₀⟩ : Call (sigN l.imp.imports.length))] = [⟨(i, p), R₀⟩] := by
  have h₁ : l.wire.length ≤ k.val ∧ k.val - l.wire.length < l.host.length := by
    have := i.isLt; omega
  simp [HLinked2.hostCalls, HLinked2.hostCall?, h₁, Fin.ext_iff]
  omega

theorem sessSpec_singleH {P : Profile} {u π u' π' : Store Nat} {j : Fin l.imp.exports.length}
    {vs : List IVal} {o : Option (List IVal)} {H : List (Call (sigN l.host.length))}
    (h : HLinked2.SessSpec P l Ie Ii u π [(j, vs)] [o] [H] u' π') :
    ∃ d : Linked2.SessRound l.toL2 Ii, d.j = j ∧ d.vs = vs ∧ d.Ok ∧
      Ii.Path P (.idle u) d.instMoves (.idle u') ∧
      HLinked2.ExpRunH P l Ie π d.dss.flatten π' ∧ d.ans = o.map .vals ∧
      l.hostCalls d.dss.flatten = H := by
  generalize hc : [(j, vs)] = cs at h
  generalize hH : [H] = Hs at h
  cases h with
  | round d hok hp he hans hr =>
    cases hr
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hc hH
    exact ⟨d, hc.1.symm, hc.2.symm, hok, hp, he, hans, hH.symm⟩

/-- **One import call, answered by the exporter or the host, is determined by its question and
compatible host answers.** -/
theorem impRelH_det {c c' : Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds ds' : List (Call (sigN l.imp.imports.length))} {π πa πb : Store Nat}
    {X Y : List (Call (sigN l.host.length))}
    (he : c.1 = c'.1) (h : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds)
    (h' : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c' ds')
    (r : HLinked2.ExpRunH (profile o) l Ie π ds πa)
    (r' : HLinked2.ExpRunH (profile o) l Ie π ds' πb)
    (hc : HostCompat (l.hostCalls ds ++ X) (l.hostCalls ds' ++ Y)) :
    c = c' ∧ ds = ds' ∧ πa = πb ∧ HostCompat X Y := by
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
    exact ⟨rfl, rfl, rfl, hc⟩
  | some ws =>
    rw [hl] at hm hm'
    obtain ⟨hk, R, rfl, rfl⟩ := hm
    obtain ⟨hk', R', rfl, rfl⟩ := hm'
    have key : R = R' ∧ πa = πb ∧ HostCompat X Y := by
      cases r with
      | ret w hw hret hr =>
        cases hr
        rw [hostCalls_one_wired hw, List.nil_append] at hc
        cases r' with
        | ret w' hw' hret' hr' =>
          cases hr'
          obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
          obtain ⟨rfl, rfl⟩ := retAt_det hret hret'
          rw [hostCalls_one_wired hw, List.nil_append] at hc
          exact ⟨rfl, rfl, hc⟩
        | trap w' hw' htrap' hr' =>
          obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
          exact (retAt_not_trapAt hret htrap').elim
        | host i hi hr' => exact (wired_not_host hw i hi).elim
      | trap w hw htrap hr =>
        cases hr
        rw [hostCalls_one_wired hw, List.nil_append] at hc
        cases r' with
        | ret w' hw' hret' hr' =>
          obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
          exact (retAt_not_trapAt hret' htrap).elim
        | trap w' hw' htrap' hr' =>
          cases hr'
          obtain rfl : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
          rw [hostCalls_one_wired hw, List.nil_append] at hc
          exact ⟨rfl, trapAt_det htrap htrap', hc⟩
        | host i hi hr' => exact (wired_not_host hw i hi).elim
      | host i hi hr =>
        cases hr
        cases r' with
        | ret w' hw' _ _ => exact (wired_not_host hw' i hi).elim
        | trap w' hw' _ _ => exact (wired_not_host hw' i hi).elim
        | host i' hi' hr' =>
          cases hr'
          obtain rfl : i = i' := Fin.ext (by simp only at hi hi'; omega)
          rw [hostCalls_one_host i hi, hostCalls_one_host i hi', List.singleton_append,
            List.singleton_append] at hc
          obtain ⟨hR, hXY⟩ := hc rfl
          exact ⟨hR, rfl, hXY⟩
    obtain ⟨hR, hπ, hXY⟩ := key
    subst hR hπ hA hA'
    exact ⟨rfl, rfl, rfl, hXY⟩

/-- **The importer's import calls and answer are determined**, given the exporter's answers and
compatible host answers. -/
theorem callsH_det {u : Store Nat} {f : Ii.F.Op} :
    ∀ (cs cs' : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss dss' : List (List (Call (sigN l.imp.imports.length))))
      (pre : List (Move Ii.E Ii.F)) (w w' : Ii.F.Ar f) (π π₁ π₂ : Store Nat),
      pre ++ (Silmaril.Wasm.Component.Reference.callMoves cs ++ [.inr (.ans f w)]) ∈
        Ii.strategy (profile o) u →
      pre ++ (Silmaril.Wasm.Component.Reference.callMoves cs' ++ [.inr (.ans f w')]) ∈
        Ii.strategy (profile o) u →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs' dss' →
      HLinked2.ExpRunH (profile o) l Ie π dss.flatten π₁ →
      HLinked2.ExpRunH (profile o) l Ie π dss'.flatten π₂ →
      HostCompat (l.hostCalls dss.flatten) (l.hostCalls dss'.flatten) →
      cs = cs' ∧ dss = dss' ∧ w = w' ∧ π₁ = π₂
  | [], [], _, _, pre, w, w', π, π₁, π₂, h, h', hr, hr', r, r', _ => by
    cases hr
    cases hr'
    cases r
    cases r'
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic h h' trivial
    simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at e
    exact ⟨rfl, rfl, e, rfl⟩
  | [], c' :: cs', _, _, pre, w, w', π, π₁, π₂, h, h', _, _, _, _, _ => by
    exfalso
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic h (mem_ask_of h') trivial
    cases e
  | c :: cs, [], _, _, pre, w, w', π, π₁, π₂, h, h', _, _, _, _, _ => by
    exfalso
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic (mem_ask_of h) h' trivial
    cases e
  | c :: cs, c' :: cs', dss, dss', pre, w, w', π, π₁, π₂, h, h', hr, hr', r, r', hc => by
    obtain ⟨ds, dss₁, hd, hr₁, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨ds', dss₁', hd', hr₁', rfl⟩ := List.forall₂_cons_left_iff.mp hr'
    rw [List.flatten_cons] at r r'
    simp only [List.flatten_cons, hostCalls_append] at hc
    obtain ⟨πa, ra, rb⟩ := HLinkedSession.expRunH_split _ _ r
    obtain ⟨πb, ra', rb'⟩ := HLinkedSession.expRunH_split _ _ r'
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
    obtain ⟨rfl, rfl, rfl, hc⟩ := impRelH_det e hd hd' ra ra' hc
    rw [hm] at h h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      callsH_det cs cs' dss₁ dss₁' _ w w' πa π₁ π₂ h h' hr₁ hr₁' rb rb' hc
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A round with host calls is a function of the stores, the call and compatible host
answers** (deterministic profiles): the outcome, the host calls and both end stores agree. -/
theorem round_detH {u π u₁ π₁ u₂ π₂ : Store Nat} {j : Fin l.imp.exports.length} {vs : List IVal}
    {o₁ o₂ : Option (List IVal)} {H₁ H₂ : List (Call (sigN l.host.length))}
    (h₁ : HLinked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₁] [H₁] u₁ π₁)
    (h₂ : HLinked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₂] [H₂] u₂ π₂)
    (hc : HostCompat H₁ H₂) :
    o₁ = o₂ ∧ H₁ = H₂ ∧ u₁ = u₂ ∧ π₁ = π₂ := by
  obtain ⟨⟨j₁, vs₁, f, cs, w, dss⟩, rfl, rfl, ⟨xs, hck, hf₁, hf₂, hrel⟩, hp, he, hans, rfl⟩ :=
    sessSpec_singleH h₁
  obtain ⟨⟨j₂, vs₂, f', cs', w', dss'⟩, hj, hv, ⟨xs', hck', hf₁', hf₂', hrel'⟩, hp', he', hans',
    rfl⟩ := sessSpec_singleH h₂
  simp only at hj hv hck hf₁ hf₂ hrel hp he hans hck' hf₁' hf₂' hrel' hp' he' hans' hc ⊢
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
  obtain ⟨rfl, rfl, rfl, rfl⟩ := callsH_det cs cs' dss dss' _ w w' π π₁ π₂ hs hs' hrel hrel' he he' hc
  refine ⟨?_, rfl, Silmaril.Wasm.Game.ScalarInstance.activation_functional hp hp', rfl⟩
  simp only [Linked2.SessRound.ans] at hans hans'
  rw [hans] at hans'
  exact Option.map_injective (fun _ _ h => Payload.vals.inj h) hans'


/-! ## Store determinism of the triples -/

/-- The refusals after a visible history are determined. -/
theorem visRun_det {h : Iface} {R R₁ R₂ : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} (h₁ : HLinked2.VisRun h R c R₁)
    (h₂ : HLinked2.VisRun h R c R₂) : R₁ = R₂ := by
  induction h₁ generalizing R₂ with
  | nil => cases h₂; rfl
  | refuse _ _ ih => cases h₂ with | refuse _ h => exact ih h
  | answer _ _ _ ih => cases h₂ with | answer _ _ h => exact ih h

theorem not_append_singleton_eq {α : Type} {c : List α} {x : α} : c ≠ c ++ [x] := by
  intro h
  have := congrArg List.length h
  simp at this

/-- **Store determinism** of the finished behaviours (deterministic profiles). -/
theorem storeDet_compFin {s : l.St} {q : Nat × Payload} {c : List (Call (sigN l.host.length))}
    {b : Payload ⊕ PUnit.{1}} {s₁ s₂ : l.St}
    (h₁ : (c, End.ret b s₁) ∈ HLinked2.compFin (profile o) l Ie Ii s q)
    (h₂ : (c, End.ret b s₂) ∈ HLinked2.compFin (profile o) l Ie Ii s q) : s₁ = s₂ := by
  cases hq : l.toL2.typedQ q with
  | none =>
    simp only [HLinked2.compFin, hq, Set.mem_singleton_iff, Prod.mk.injEq, End.ret.injEq] at h₁ h₂
    rw [h₁.2.2, h₂.2.2]
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    simp only [HLinked2.compFin, hq] at h₁ h₂
    rcases h₁ with ⟨o₁, u₁, π₁, R₁, hs₁, hv₁, he₁⟩ | ⟨m₁, u₁, π₁, R₁, hs₁, hv₁, -, he₁⟩ |
        ⟨_, _, _, he₁⟩ <;>
      rcases h₂ with ⟨o₂, u₂, π₂, R₂, hs₂, hv₂, he₂⟩ | ⟨m₂, u₂, π₂, R₂, hs₂, hv₂, -, he₂⟩ |
        ⟨_, _, _, he₂⟩ <;>
      simp only [End.ret.injEq, reduceCtorEq] at he₁ he₂
    · obtain ⟨-, rfl⟩ := he₁
      obtain ⟨-, rfl⟩ := he₂
      obtain ⟨-, -, rfl, rfl⟩ := round_detH hs₁ hs₂ (hostCompat_refl _)
      rw [visRun_det hv₁ hv₂]
    · obtain ⟨-, h, -, -⟩ :=
        round_detH hs₁ hs₂ (by simpa using hostCompat_append c (X := []) (Y := [_]) trivial)
      exact (not_append_singleton_eq h).elim
    · obtain ⟨-, h, -, -⟩ :=
        round_detH hs₂ hs₁ (by simpa using hostCompat_append c (X := []) (Y := [_]) trivial)
      exact (not_append_singleton_eq h).elim
    · obtain ⟨-, rfl⟩ := he₁
      obtain ⟨-, rfl⟩ := he₂
      obtain ⟨-, -, rfl, rfl⟩ := round_detH hs₁ hs₂ (hostCompat_append c hostCompat_refuse)
      rw [visRun_det hv₁ hv₂]

/-- **Store determinism** of the host-realizable triple (deterministic profiles). -/
theorem storeDet_compTripleS :
    StratThread.StoreDet (HLinked2.compTripleS (profile o) l Ie Ii) :=
  fun _ _ _ _ _ _ h₁ h₂ => storeDet_compFin h₁ h₂

/-- **Store determinism** of the open triple (deterministic profiles). -/
theorem storeDet_compTripleO :
    StratThread.StoreDet (HLinked2.compTripleO (profile o) l Ie Ii) := by
  intro s q c b s₁ s₂ h₁ h₂
  change (c.map StratLegal.liftCall, End.ret b s₁) ∈ HLinked2.compFinO (profile o) l Ie Ii s q
    at h₁
  change (c.map StratLegal.liftCall, End.ret b s₂) ∈ HLinked2.compFinO (profile o) l Ie Ii s q
    at h₂
  cases hq : l.toL2.typedQ q with
  | none =>
    simp only [HLinked2.compFinO, hq, Set.mem_singleton_iff, Prod.mk.injEq, End.ret.injEq]
      at h₁ h₂
    rw [h₁.2.2, h₂.2.2]
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    simp only [HLinked2.compFinO, hq] at h₁ h₂
    rcases h₁ with ⟨o₁, u₁, π₁, hs₁, he₁⟩ | ⟨_, he₁⟩ <;>
      rcases h₂ with ⟨o₂, u₂, π₂, hs₂, he₂⟩ | ⟨_, he₂⟩ <;>
      simp only [End.ret.injEq, reduceCtorEq] at he₁ he₂
    obtain ⟨-, rfl⟩ := he₁
    obtain ⟨-, rfl⟩ := he₂
    obtain ⟨-, -, rfl, rfl⟩ := round_detH hs₁ hs₂ (hostCompat_refl _)
    rfl

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
