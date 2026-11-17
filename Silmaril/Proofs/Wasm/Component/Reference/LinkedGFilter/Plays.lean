module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.Filter
public import Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.Main

/-!
# The session object of a linked component with an abstract exporter: finite plays

* `rounds_of_run_filter`, `run_filter_of_rounds`: the completed rounds of an exporter's session
  triple (`ExpSpec.sessTripleS`) are rounds whose ill-typed questions trap, the state unchanged,
  and whose typed rounds are a session of the exporter (`ExpSpec.Run`);
* `pubPlays_toExp`: for `g.toExp Ii` meeting `ExpSpec.Adeq`, the plays of `g.toComp.den` at
  `sigU` are the plays of `(g.toExp Ii).session P` asking questions in range, read at `sigU`.
  The ill-typed rounds go through `filterU_iff` (`Filter`), the typed ones through
  `ExpSpec.Adeq`;
* `linkedG_pubPlays_compSession`: the same for `LinkedG.compSession` (`LinkedG.toExp_adeq`);
  `linkedG_compSession_eq_pubPlays`, `linkedG_pubPlays_of_refSessEquivFull`: equal session
  objects, hence (at `profile o`, `LinkedG.compSession_inj_full`) the full resumable-session
  equivalence, give the same IR plays.

The proof follows #746's `Linked2.pubPlays_compSession` (`LinkedSessionObs.Plays`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter

open Classical
open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds roundsMoves roundMoves)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionStrat
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession
  (ret_mem_typed ret_mem_untyped sumAns_inj noPlainTrap_sessTripleS)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Rounds of an exporter's triple -/

section Rounds

variable {P : Profile} {e : ExpSpec}

theorem ofAns_eq (A : Option Payload) : SessionStrat.ofAns A = ExpSpec.sumAns A := by
  cases A <;> rfl

/-- **A session of the typed rounds, the ill-typed ones trapping, is completed rounds.** -/
theorem rounds_of_run_filter : ∀ {s s' : e.St} {M : List URound},
    (∀ x ∈ M, ¬ e.TypedQ x.1 → x.2 = none) →
    e.Run P s (M.filter fun x => decide (e.TypedQ x.1)) s' →
    Rounds (e.sessTripleS P) s (M.map ofRound) s'
  | s, s', [], _, h => by
    rw [List.filter_nil] at h
    cases h
    exact .nil _
  | s, s', x :: M, hb, h => by
    have hb' : ∀ y ∈ M, ¬ e.TypedQ y.1 → y.2 = none :=
      fun y hy => hb y (List.mem_cons_of_mem _ hy)
    show Rounds _ s ((x.1, [], SessionStrat.ofAns x.2) :: M.map ofRound) s'
    by_cases hq : e.TypedQ x.1
    · rw [List.filter_cons_of_pos (by simpa using hq)] at h
      cases h with
      | cons hs h' =>
        exact .cons ((ret_mem_typed hq).mpr ⟨rfl, x.2, hs, ofAns_eq x.2⟩)
          (rounds_of_run_filter hb' h')
    · rw [List.filter_cons_of_neg (by simpa using hq)] at h
      have hx : x.2 = none := hb x List.mem_cons_self hq
      exact .cons ((ret_mem_untyped hq).mpr ⟨rfl, by simp [hx, SessionStrat.ofAns], rfl⟩)
        (rounds_of_run_filter hb' h)

/-- **Completed rounds are a session of the typed rounds, the ill-typed ones trapping.** -/
theorem run_filter_of_rounds : ∀ {s s' : e.St} {M : List URound},
    Rounds (e.sessTripleS P) s (M.map ofRound) s' →
    (∀ x ∈ M, ¬ e.TypedQ x.1 → x.2 = none) ∧
      e.Run P s (M.filter fun x => decide (e.TypedQ x.1)) s'
  | s, s', [], h => by
    have h₀ : Rounds (e.sessTripleS P) s [] s' := h
    cases h₀
    exact ⟨(fun _ h => nomatch h), .nil _⟩
  | s, s', x :: M, h => by
    have h₀ : Rounds (e.sessTripleS P) s
        ((x.1, [], SessionStrat.ofAns x.2) :: M.map ofRound) s' := h
    cases h₀ with
    | cons hm h' =>
      obtain ⟨ih₁, ih₂⟩ := run_filter_of_rounds h'
      by_cases hq : e.TypedQ x.1
      · obtain ⟨-, R, hs, hR⟩ := (ret_mem_typed hq).mp hm
        rw [ofAns_eq] at hR
        obtain rfl := sumAns_inj hR
        refine ⟨fun y hy hny => ?_, ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact absurd hq hny
          · exact ih₁ y hy hny
        · rw [List.filter_cons_of_pos (by simpa using hq)]
          exact .cons hs ih₂
      · obtain ⟨-, hb, rfl⟩ := (ret_mem_untyped hq).mp hm
        have hx : x.2 = none := by
          cases ex : x.2 with
          | none => rfl
          | some p =>
            rw [ex] at hb
            cases hb
        refine ⟨fun y hy hny => ?_, ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact ih₁ y hy hny
        · rw [List.filter_cons_of_neg (by simpa using hq)]
          exact ih₂

end Rounds

/-! ## Finite plays -/

section Plays

variable {P : Profile} {g : LinkedG} {Ii : SInst}

theorem filter_typed (M : List URound) :
    ∀ r ∈ M.filter (fun x => decide ((g.toExp Ii).TypedQ x.1)), (g.toExp Ii).Typed r := by
  intro r hr
  exact of_decide_eq_true (List.mem_filter.mp hr).2

/-- **The IR plays are the in-range plays of the session object of `g.toExp Ii`.** -/
theorem pubPlays_toExp (hi : g.imp.Good) (he : (g.toExp Ii).Adeq P) :
    pubPlays (g.toComp.den (impSem P)) =
      {q | ∃ p ∈ ((g.toExp Ii).session P).toStrategy, AskedIn g.imp.exports.length p ∧
        p.map sessMove = q} := by
  have key : ∀ L : List (Round (sigN g.toComp.exports.length)),
      exportRounds L ∈ g.toComp.den (impSem P) →
      ∃ s', Rounds ((g.toExp Ii).sessTripleS P) (g.toExp Ii).init
        ((L.map Round.forget).map ofRound) s' := by
    intro L hL
    have hU := (den_iffG L).mp hL
    obtain ⟨hbad, hT⟩ := (filterU_iff hi Ii (forget_lt L)).mp hU
    obtain ⟨s', hR⟩ := he.bwd _ (filter_typed _) (by rw [LinkedG.uMoves_eq]; exact hT)
    exact ⟨s', rounds_of_run_filter hbad hR⟩
  have himg : ∀ L : List (Round (sigN g.toComp.exports.length)),
      ((roundsMoves ((L.map Round.forget).map ofRound)).map StratSession.relMove).map sessMove =
        (exportRounds L).map forgetMove := by
    intro L
    rw [exportRounds_eq, List.map_map, map_roundsMoves, map_toRound_ofRound,
      map_forgetMove_twos]
  have hlt₀ : ∀ q : (sigN g.toComp.exports.length).Op, q.1.val < g.imp.exports.length := by
    intro q
    rw [← LinkedG.exports_length_toComp]
    exact q.1.isLt
  ext q
  constructor
  · rintro ⟨p', hp', rfl⟩
    rcases linkedG_den_shape P g hp' with ⟨L, rfl⟩ | ⟨L, q₀, rfl⟩
    · obtain ⟨s', hR⟩ := key L hp'
      refine ⟨_, StratSession.mem_threadS.mpr ⟨_, StratThread.mem_threadT.mpr
        ⟨_, StratThread.run_idle_iff.mpr ⟨_, rfl, hR⟩⟩, rfl⟩, fun q hq => ?_, himg L⟩
      have h := ask_mem_map_sessMove.mpr hq
      rw [himg, exportRounds_eq, map_forgetMove_twos] at h
      obtain ⟨x, hx, rfl⟩ := ask_mem_twos h
      exact forget_lt L x hx
    · have hp₀ : exportRounds L ∈ g.toComp.den (impSem P) :=
        (g.toComp.den (impSem P)).of_prefix hp' (List.prefix_append _ _)
      obtain ⟨s', hR⟩ := key L hp₀
      have hrun := (StratThread.run_idle_iff.mpr ⟨_, rfl, hR⟩).append
        (.cons (StratThread.TStep.ask _ (q₀.1.val, q₀.2)) (.nil _))
      have himg' : (((roundsMoves ((L.map Round.forget).map ofRound)) ++
          ([Sum.inr (Ev.ask (q₀.1.val, q₀.2))] :
            List (Move (sigN 0) (sig1 (Nat × Payload) (Payload ⊕ PUnit.{1}))))).map
              StratSession.relMove).map sessMove =
          (exportRounds L ++ ([Sum.inr (Ev.ask q₀)] :
            List (Move (sigN 0) (sigN g.toComp.exports.length)))).map forgetMove := by
        rw [List.map_append, List.map_append, himg, List.map_append]
        rfl
      refine ⟨_, StratSession.mem_threadS.mpr ⟨_, StratThread.mem_threadT.mpr ⟨_, hrun⟩, rfl⟩,
        fun q hq => ?_, himg'⟩
      have h := ask_mem_map_sessMove.mpr hq
      rw [himg', List.map_append, exportRounds_eq, map_forgetMove_twos] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨x, hx, rfl⟩ := ask_mem_twos h
        exact forget_lt L x hx
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, forgetMove, Sum.inr.injEq,
          Ev.ask.injEq] at h
        subst h
        exact hlt₀ q₀
  · rintro ⟨p, hp, hask, rfl⟩
    obtain ⟨p₀, ⟨y, hy⟩, rfl⟩ := StratSession.mem_threadS.mp hp
    obtain ⟨rs, s', hR, hshape⟩ := trun_shape noPlainTrap_sessTripleS hy
    have hR' : Rounds ((g.toExp Ii).sessTripleS P) (g.toExp Ii).init
        ((rs.map toRound).map ofRound) s' := by
      rw [map_ofRound_toRound]
      exact hR
    obtain ⟨hbad, hrun⟩ := run_filter_of_rounds hR'
    have hlt : ∀ x ∈ rs.map toRound, x.1.1 < g.imp.exports.length := by
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
    have hT := he.fwd _ _ hrun
    rw [LinkedG.uMoves_eq] at hT
    have hU : twos (rs.map toRound) ∈ g.toComp.denU (impSem P) :=
      (filterU_iff hi Ii hlt).mpr ⟨hbad, hT⟩
    obtain ⟨L, hL⟩ := exists_forget (n := g.toComp.exports.length) (rs.map toRound)
      fun x hx => by rw [LinkedG.exports_length_toComp]; exact hlt x hx
    have hden : exportRounds L ∈ g.toComp.den (impSem P) := (den_iffG L).mpr (hL ▸ hU)
    have hden' : twos L ∈ g.toComp.den (impSem P) := by
      have h := hden
      rw [exportRounds_eq] at h
      exact h
    rcases hshape with ⟨rfl, -⟩ | ⟨a, rfl, -⟩
    · refine ⟨exportRounds L, hden, ?_⟩
      rw [exportRounds_eq, map_forgetMove_twos, hL, List.map_map, map_roundsMoves]
    · have ha : a.1 < g.toComp.exports.length := by
        rw [LinkedG.exports_length_toComp]
        refine hask a (List.mem_map.mpr ⟨.inr (.ask a), ?_, rfl⟩)
        simp
      let q' : (sigN g.toComp.exports.length).Op := (⟨a.1, ha⟩, a.2)
      refine ⟨twos L ++ [.inr (.ask q')], ?_, ?_⟩
      · exact (g.toComp.den (impSem P)).receptive hden' (path_twos _) (Step.ask q') trivial
      · rw [List.map_append, map_forgetMove_twos, hL, List.map_append, List.map_append,
          List.map_map, map_roundsMoves]
        rfl

/-- **The IR plays are the in-range plays of the session object of a linked component.** -/
theorem linkedG_pubPlays_compSession (P : Profile) (he : g.exp.Adeq P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    pubPlays (g.toComp.den (impSem P)) =
      {q | ∃ p ∈ (LinkedG.compSession P g).toStrategy, AskedIn g.imp.exports.length p ∧
        p.map sessMove = q} := by
  rw [LinkedGSession.compSession_eq_session hIi]
  exact pubPlays_toExp hi (LinkedG.toExp_adeq he hi hIi hw)

/-- Linked components with the same export count and equal session objects have the same IR
plays. -/
theorem linkedG_compSession_eq_pubPlays {g' : LinkedG} {Ii' : SInst} (he : g.exp.Adeq P)
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) (he' : g'.exp.Adeq P)
    (hi' : g'.imp.Good) (hIi' : g'.imp.mod.IsInst Ii') (hw' : g'.WireTy)
    (len : g.imp.exports.length = g'.imp.exports.length)
    (h : LinkedG.compSession P g = LinkedG.compSession P g') :
    pubPlays (g.toComp.den (impSem P)) = pubPlays (g'.toComp.den (impSem P)) := by
  rw [linkedG_pubPlays_compSession P he hi hIi hw, linkedG_pubPlays_compSession P he' hi' hIi' hw',
    h, len]

open Silmaril.Wasm.SingleThreaded (GrowOracle profile) in
/-- **The full resumable-session equivalence gives the same IR plays** (`profile o`): through
`LinkedG.compSession_inj_full`. -/
theorem linkedG_pubPlays_of_refSessEquivFull {o : GrowOracle} {prof : ProfileKind} {g' : LinkedG}
    (hg : g.ProfOk o) (hg' : g'.ProfOk o) (h : LinkedG.RefSessEquivFull (profile o) prof g g') :
    pubPlays (g.toComp.den (impSem (profile o))) =
      pubPlays (g'.toComp.den (impSem (profile o))) := by
  obtain ⟨hst, heq⟩ := (LinkedGSession.compSession_inj_full hg hg').mp h
  obtain ⟨Ii, hIi⟩ := hg.link.inst.inst
  obtain ⟨Ii', hIi'⟩ := hg'.link.inst.inst
  have len : g.imp.exports.length = g'.imp.exports.length := by
    simpa using congrArg List.length hst
  exact linkedG_compSession_eq_pubPlays hg.adeq hg.link.good hIi hg.link.wireTy hg'.adeq
    hg'.link.good hIi' hg'.link.wireTy len heq

end Plays

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter
