module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Triple
public import Silmaril.Wasm.Component.Reference.LinkedSessionAdeq.Thms

/-!
# The session object of a linked component: rounds and finite plays

* `spec_of_roundsL`, `rounds_of_specL`: the completed rounds of the linked triple from a pair of
  stores are the `Linked2.SessSpec` sessions of their typed calls, the untyped questions trapping
  at once with both stores unchanged (`ShapedL`);
* `compSession_eq`: the session object is the threading of the triple of the instances;
* `pubPlays_compSession`: the plays of `l.toComp.den (impSem P)` at `sigU` are the plays of the
  session object asking questions in range, read at `sigU`. Through #726's `den_inv`,
  `den_read`, `den_of_sess` (ill-typed rounds) and #724's `Linked2.sessIR_iff`.
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

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {l : Linked2} {Ie Ii : SInst}

/-! ## Rounds and specification sessions -/

/-- Rounds whose untyped questions trap and whose typed calls answer values or a trap. -/
def ShapedL (l : Linked2) (Lu : List (Round sigU)) : Prop :=
  ∀ x ∈ Lu, (l.typedQ x.1 = none → x.2 = none) ∧
    (∀ q, l.typedQ x.1 = some q → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws))

theorem ansOut_optAns_outAns (o : Option (List IVal)) : ansOut (optAns (outAns o)) = o := by
  cases o <;> rfl

theorem shapedL_of {Lu : List (Round sigU)}
    (hbad : ∀ x ∈ Lu, good l x.1 = false → x.2 = none)
    (hform : ∀ x ∈ Lu, good l x.1 = true → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws)) :
    ShapedL l Lu := fun x hx =>
  ⟨fun h => hbad x hx (by simp [good, h]), fun _ h => hform x hx (by simp [good, h])⟩

theorem bad_of_shapedL {Lu : List (Round sigU)} (h : ShapedL l Lu) :
    ∀ x ∈ Lu, good l x.1 = false → x.2 = none :=
  fun x hx hb => (h x hx).1 (good_false hb)

theorem form_of_shapedL {Lu : List (Round sigU)} (h : ShapedL l Lu) :
    ∀ x ∈ Lu, good l x.1 = true → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws) := fun x hx hg => by
  obtain ⟨q, hq⟩ := good_true hg
  exact (h x hx).2 q hq

/-- **Completed rounds are specification sessions** on their typed calls. -/
theorem spec_of_roundsL :
    ∀ {s s' : Store Nat × Store Nat}
      {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))},
      Rounds (Linked2.compTripleS P l Ie Ii) s rs s' →
      Linked2.SessSpec P l Ie Ii s.2 s.1 (sessCallsL l (rs.map toRound))
          (sessOutsL l (rs.map toRound)) s'.2 s'.1 ∧
        SimpleI.TypedCalls l.imp (sessCallsL l (rs.map toRound)) ∧ ShapedL l (rs.map toRound)
  | _, _, _, .nil s => ⟨.nil _ _, fun _ h => by simp [sessCallsL] at h, fun _ h => by simp at h⟩
  | s, _, _, .cons (a := q) (c := c) (b := b) hm hr => by
    obtain ⟨hspec, hty, hsh⟩ := spec_of_roundsL hr
    rw [List.map_cons]
    cases hq : l.typedQ q with
    | none =>
      have hq' : l.typedQ (toRound (q, c, b)).1 = none := hq
      have e := (mem_compFin_none hq).mp hm
      simp only [Prod.mk.injEq, End.ret.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      rw [sessCallsL_none hq', sessOutsL_none hq']
      refine ⟨hspec, hty, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨fun _ => rfl, fun _ h => (by rw [hq'] at h; cases h)⟩
      · exact hsh x hx
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      have hq' : l.typedQ (toRound (q, c, b)).1 = some (j, vs) := hq
      obtain ⟨-, ⟨o, π', u', h₁, he⟩ | ⟨-, he⟩⟩ := (mem_compFin_some hq).mp hm <;>
        simp only [End.ret.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [sessCallsL_some hq', sessOutsL_some hq']
      have ho : ansOut (toRound (q, c, outAns o)).2 = o := ansOut_optAns_outAns o
      rw [ho]
      refine ⟨sessSpec_cons_iff.mpr ⟨_, _, h₁, hspec⟩, fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact (typedQ_some hq).2
        · exact hty x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · refine ⟨fun h => (by rw [hq'] at h; cases h), fun _ _ => ?_⟩
          cases o with
          | none => exact .inl rfl
          | some ws => exact .inr ⟨ws, rfl⟩
        · exact hsh x hx

/-- **Specification sessions are completed rounds**, the untyped questions trapping at once. -/
theorem rounds_of_specL :
    ∀ {Lu : List (Round sigU)} {π u π' u' : Store Nat}, ShapedL l Lu →
      Linked2.SessSpec P l Ie Ii u π (sessCallsL l Lu) (sessOutsL l Lu) u' π' →
      Rounds (Linked2.compTripleS P l Ie Ii) (π, u) (Lu.map ofRound) (π', u')
  | [], _, _, _, _, _, h => by
    cases h
    exact .nil _
  | ⟨q, A⟩ :: Lu, π, u, π', u', hsh, h => by
    have hsh' : ShapedL l Lu := fun x hx => hsh x (List.mem_cons_of_mem _ hx)
    obtain ⟨hnone, hsome⟩ := hsh _ List.mem_cons_self
    rw [List.map_cons]
    cases hq : l.typedQ q with
    | none =>
      rw [sessCallsL_none hq, sessOutsL_none hq] at h
      have hA : A = none := hnone hq
      subst hA
      exact .cons ((mem_compFin_none hq).mpr rfl) (rounds_of_specL hsh' h)
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      rw [sessCallsL_some hq, sessOutsL_some hq] at h
      obtain ⟨u₁, π₁, h₁, h₂⟩ := sessSpec_cons_iff.mp h
      have hA : ofAns A = outAns (ansOut A) := by
        rcases hsome _ hq with hA | ⟨ws, hA⟩
        · have hA' : A = none := hA
          subst hA'
          rfl
        · have hA' : A = some (.vals ws) := hA
          subst hA'
          rfl
      refine .cons ((mem_compFin_some hq).mpr ⟨rfl, .inl ⟨ansOut A, π₁, u₁, h₁, ?_⟩⟩)
        (rounds_of_specL hsh' h₂)
      show End.ret (ofAns A) (π₁, u₁) = _
      rw [hA]

/-- Divergent behaviours of the triple are diverging typed calls. -/
theorem div_iffL {s : Store Nat × Store Nat} {q : Nat × Payload} {c : List (Call (sigN 0))} :
    (c, End.div) ∈ (Linked2.compTripleS P l Ie Ii).1 s q ↔
      ∃ j vs, l.typedQ q = some (j, vs) ∧ Linked2.RoundDiv P l Ie Ii s.2 s.1 j vs := by
  constructor
  · intro hm
    cases hq : l.typedQ q with
    | none => cases (mem_compFin_none hq).mp hm
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      obtain ⟨-, ⟨_, _, _, _, he⟩ | ⟨hd, -⟩⟩ := (mem_compFin_some hq).mp hm
      · cases he
      · exact ⟨j, vs, rfl, hd⟩
  · rintro ⟨j, vs, hq, hd⟩
    exact (mem_compFin_some hq).mpr ⟨calls_nil c, .inr ⟨hd, rfl⟩⟩

/-! ## Typed sessions as rounds -/

theorem sessCallsL_sessLu :
    ∀ {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))},
      SimpleI.TypedCalls l.imp calls → calls.length = outs.length →
      sessCallsL l (sessLu calls outs) = calls ∧ sessOutsL l (sessLu calls outs) = outs
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | (j, vs) :: calls, o :: outs, ht, hlen => by
    have hq : l.typedQ (j.val, .vals vs) = some (j, vs) := typedQ_typed (ht _ List.mem_cons_self)
    obtain ⟨e₁, e₂⟩ := sessCallsL_sessLu (calls := calls) (outs := outs)
      (fun q hq => ht q (List.mem_cons_of_mem _ hq)) (by simpa using hlen)
    refine ⟨?_, ?_⟩
    · show sessCallsL l (⟨(j.val, .vals vs), o.map .vals⟩ :: sessLu calls outs) = _
      rw [sessCallsL_some hq, e₁]
    · show sessOutsL l (⟨(j.val, .vals vs), o.map .vals⟩ :: sessLu calls outs) = _
      rw [sessOutsL_some hq, e₂]
      cases o <;> rfl

theorem shapedL_sessLu :
    ∀ {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))},
      SimpleI.TypedCalls l.imp calls → ShapedL l (sessLu calls outs)
  | [], _, _ => fun _ h => nomatch h
  | _ :: _, [], _ => fun _ h => nomatch h
  | (j, vs) :: calls, o :: outs, ht => by
    have hq : l.typedQ (j.val, .vals vs) = some (j, vs) := typedQ_typed (ht _ List.mem_cons_self)
    have ih := shapedL_sessLu (calls := calls) (outs := outs)
      (fun q hq => ht q (List.mem_cons_of_mem _ hq))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨fun h => (by rw [hq] at h; cases h), fun _ _ => ?_⟩
      cases o with
      | none => exact .inl rfl
      | some ws => exact .inr ⟨ws, rfl⟩
    · exact ih x hx

/-- A specification session on typed calls is completed rounds. -/
theorem rounds_of_sessSpecL {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {u π u' π' : Store Nat}
    (hspec : Linked2.SessSpec P l Ie Ii u π calls outs u' π')
    (ht : SimpleI.TypedCalls l.imp calls) :
    Rounds (Linked2.compTripleS P l Ie Ii) (π, u) ((sessLu calls outs).map ofRound) (π', u') ∧
      sessCallsL l (sessLu calls outs) = calls ∧ sessOutsL l (sessLu calls outs) = outs := by
  obtain ⟨e₁, e₂⟩ := sessCallsL_sessLu ht (LinkedSessionRef.sessSpec_length hspec)
  refine ⟨rounds_of_specL (shapedL_sessLu ht) ?_, e₁, e₂⟩
  rw [e₁, e₂]
  exact hspec

/-! ## The session object -/

theorem compSession_eq (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    Linked2.compSession P l =
      StratSession.threadS (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store) := by
  unfold Linked2.compSession
  split
  · rename_i h
    obtain ⟨h₁, h₂⟩ := h.choose_spec.choose_spec
    rw [ImpModule.IsInst.unique h₂ hIi, NumModule.IsInst.unique h₁ hIe]
  · rename_i h
    exact absurd ⟨Ie, Ii, hIe, hIi⟩ h

theorem forget_mem_ltL {L : List (Round (sigN l.toComp.exports.length))} {x : Round sigU}
    (hx : x ∈ L.map Round.forget) : x.1.1 < l.imp.exports.length := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  rw [← Linked2.exports_length_toComp]
  exact y.1.1.isLt

/-- **The IR plays are the in-range plays of the session object.** -/
theorem pubPlays_compSession (P : Profile) (l : Linked2) (hl : l.Adequate) :
    pubPlays (l.toComp.den (impSem P)) =
      {q | ∃ p ∈ (Linked2.compSession P l).toStrategy, AskedIn l.imp.exports.length p ∧
        p.map sessMove = q} := by
  obtain ⟨Ie, hIe⟩ := hl.expInst.inst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  rw [compSession_eq hIe hIi]
  have key : ∀ L : List (Round (sigN l.toComp.exports.length)),
      twos L ∈ l.toComp.den (impSem P) →
      ∃ s', Rounds (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store)
        ((L.map Round.forget).map ofRound) s' := by
    intro L hL
    obtain ⟨hbad, hform, -⟩ := den_inv hl.impGood hL
    obtain ⟨-, -, hlen, ht, hmv⟩ := den_read hl.impGood hL
    obtain ⟨u', π', hS⟩ := (Linked2.sessIR_iff P l hl hIe hIi _ _ ht hlen).mp hmv
    exact ⟨(π', u'), rounds_of_specL (shapedL_of hbad hform) hS⟩
  have himg : ∀ L : List (Round (sigN l.toComp.exports.length)),
      ((roundsMoves ((L.map Round.forget).map ofRound)).map StratSession.relMove).map sessMove =
        (twos L).map forgetMove := by
    intro L
    rw [List.map_map, map_roundsMoves, map_toRound_ofRound, map_forgetMove_twos]
  ext q
  constructor
  · rintro ⟨p', hp', rfl⟩
    rcases den_shape hp' with ⟨L, rfl⟩ | ⟨q₀, L, rfl⟩
    · obtain ⟨s', hR⟩ := key L hp'
      refine ⟨_, StratSession.mem_threadS.mpr ⟨_, StratThread.mem_threadT.mpr
        ⟨_, StratThread.run_idle_iff.mpr ⟨_, rfl, hR⟩⟩, rfl⟩, fun q hq => ?_, himg L⟩
      have h := ask_mem_map_sessMove.mpr hq
      rw [himg, map_forgetMove_twos] at h
      obtain ⟨x, hx, rfl⟩ := ask_mem_twos h
      exact forget_mem_ltL hx
    · have hp₀ : twos L ∈ l.toComp.den (impSem P) :=
        (l.toComp.den (impSem P)).of_prefix hp' (List.prefix_append _ _)
      obtain ⟨s', hR⟩ := key L hp₀
      have hrun := (StratThread.run_idle_iff.mpr ⟨_, rfl, hR⟩).append
        (.cons (StratThread.TStep.ask _ (q₀.1.val, q₀.2)) (.nil _))
      have himg' : (((roundsMoves ((L.map Round.forget).map ofRound)) ++
          ([Sum.inr (Ev.ask (q₀.1.val, q₀.2))] :
            List (Move (sigN 0) (sig1 (Nat × Payload) (Payload ⊕ PUnit.{1}))))).map
              StratSession.relMove).map sessMove =
          (twos L ++ ([Sum.inr (Ev.ask q₀)] :
            List (Move (sigN 0) (sigN l.toComp.exports.length)))).map forgetMove := by
        rw [List.map_append, List.map_append, himg, List.map_append]
        rfl
      refine ⟨_, StratSession.mem_threadS.mpr ⟨_, StratThread.mem_threadT.mpr ⟨_, hrun⟩, rfl⟩,
        fun q hq => ?_, himg'⟩
      have h := ask_mem_map_sessMove.mpr hq
      rw [himg', List.map_append, map_forgetMove_twos] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨x, hx, rfl⟩ := ask_mem_twos h
        exact forget_mem_ltL hx
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, forgetMove, Sum.inr.injEq,
          Ev.ask.injEq] at h
        subst h
        show q₀.1.val < l.imp.exports.length
        rw [← Linked2.exports_length_toComp]
        exact q₀.1.isLt
  · rintro ⟨p, hp, hask, rfl⟩
    obtain ⟨p₀, ⟨y, hy⟩, rfl⟩ := StratSession.mem_threadS.mp hp
    obtain ⟨rs, s', hR, hshape⟩ := trun_shape noPlainTrap_compTripleS hy
    obtain ⟨hspec, ht, hsh⟩ := spec_of_roundsL hR
    have hlt : ∀ x ∈ rs.map toRound, x.1.1 < l.imp.exports.length := by
      intro x hx
      refine hask x.1 (ask_mem_map_sessMove.mp ?_)
      rw [List.map_map]
      have hmem : (Sum.inr (Ev.ask x.1) : Move (sigN 0) sigU) ∈
          (roundsMoves rs).map (sessMove ∘ StratSession.relMove) := by
        rw [map_roundsMoves]
        exact twos_ask_mem hx
      rcases hshape with ⟨rfl, -⟩ | ⟨a, rfl, -⟩
      · exact hmem
      · rw [List.map_append]
        exact List.mem_append_left _ hmem
    have hmv := Linked2.sess_specToIR hl.expGood hl.impGood hIe hIi hspec
    obtain ⟨e, -, -⟩ := read_filter l (rs.map toRound) (form_of_shapedL hsh)
    obtain ⟨L, hL⟩ := exists_forget (n := l.toComp.exports.length) (rs.map toRound)
      fun x hx => by rw [Linked2.exports_length_toComp]; exact hlt x hx
    have hden : twos L ∈ l.toComp.den (impSem P) :=
      den_of_sess hl.impGood (hL ▸ bad_of_shapedL hsh) (hL ▸ e) hmv
    rcases hshape with ⟨rfl, -⟩ | ⟨a, rfl, -⟩
    · refine ⟨twos L, hden, ?_⟩
      rw [map_forgetMove_twos, hL, List.map_map, map_roundsMoves]
    · have ha : a.1 < l.toComp.exports.length := by
        rw [Linked2.exports_length_toComp]
        refine hask a (List.mem_map.mpr ⟨.inr (.ask a), ?_, rfl⟩)
        simp
      let q' : (sigN l.toComp.exports.length).Op := (⟨a.1, ha⟩, a.2)
      refine ⟨twos L ++ [.inr (.ask q')], ?_, ?_⟩
      · exact (l.toComp.den (impSem P)).receptive hden (path_twos _) (Step.ask q') trivial
      · rw [List.map_append, map_forgetMove_twos, hL, List.map_append, List.map_append,
          List.map_map, map_roundsMoves]
        rfl

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs
