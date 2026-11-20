module

public import Silmaril.Proofs.Wasm.Component.InstSem.Wired
public import Silmaril.Proofs.Wasm.Component.InstEngine.Converse

/-!
# A node's instantiation play, down to its engine run

* `coreNodeI_inst_inv`: an instantiation round of a core node is an instantiation round of its
  module whose import calls are answered by the wiring (`implsN`);
* `run_starting_inv_fail`: a run of the start phase answering `fail` is a start run that traps
  (the counterpart of `InstEngine.run_starting_inv`);
* `engine_inst_inv`: an instantiation play of an engine instance is `EngineInst`;
* `nodesInst_fail_nil`: a failing instantiation without calls fails at a node `k`: the nodes
  before it are ready and the node `k` fails, each without a call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.Component.Reference (Engine)

variable {M : Type} [CoreModule M]

/-- **A core node's instantiation round is its module's**, the module's import calls answered by
the wiring. -/
theorem coreNodeI_inst_inv {C : CoreSemI M} {e : Nat} {m : M} {args : List Impl}
    {w : List (Call sigU)} {a : InstAns Unit}
    (h : (instRound (F := sigU) w a).moves ∈ coreNodeI C e m args) :
    ∃ ys : List (Round sigU (sigN (CoreModule.imports m).length)),
      (instRound (F := CoreIface.sig (CoreModule.exports m)) (ys.map Round.call) a).moves ∈
        C.sem m ∧
      (∀ y ∈ ys, Prog.Runs (implsN e args (CoreModule.imports m).length y.q) y.cs y.a) ∧
      w = allCalls ys := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := (Strategy.ofHandler _).legal hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨ss, ts, rfl, rfl, hZ⟩ := zip_rounds_inv [instRound w a] ps pt
    (by simpa only [roundsMoves, List.append_nil] using hz)
  obtain ⟨xs, _, _, rfl, rfl, hc, hz'⟩ := zipR_cons_inv hZ
  cases hz'
  rw [List.append_nil] at hs
  simp only at hc
  obtain ⟨s', hs', t', ht', hz''⟩ := ht
  obtain ⟨_, ps'⟩ := Strategy.legal _ hs'
  obtain ⟨_, pt'⟩ := Strategy.legal _ ht'
  obtain ⟨us, vs, rfl, rfl, hZ'⟩ := zip_rounds_inv
    [(⟨none, xs.map Round.call, a⟩ : Round _ sigUI)]
    ps' pt' (by simpa only [roundsMoves, List.append_nil] using hz'')
  obtain ⟨us₀, _, _, rfl, rfl, hc', hz₃⟩ := zipR_cons_inv hZ'
  cases hz₃
  rw [List.append_nil] at hs'
  have h₀ := runs_of_ofHandler_rounds ht' _ (.head _)
  simp only [liftH] at h₀ hc'
  rcases us₀ with _ | ⟨⟨uq, ucs, ua⟩, _ | _⟩
  · cases h₀
  · cases h₀ with
    | call h₁ =>
      cases h₁
      simp only [allCalls, List.append_nil] at hc'
      subst hc'
      refine ⟨xs, ?_, runs_of_ofHandler_rounds hs, hc⟩
      simpa only [roundsMoves, List.append_nil] using hs'
  · cases h₀ with
    | call h₁ => cases h₁

variable {E : Engine} {I : Option (IInstance E)} {imps exps : CoreIface}

/-- **A run of the start phase answering `fail`** is a start run that traps. -/
theorem run_starting_inv_fail :
    ∀ (cs : List (Σ _ : (sigN imps.length).Op, Option Payload)) {s : E.Store Nat}
      {t : E.Thread Nat} {rest : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))}
      {z : IState E imps.length exps.length},
    (engineLTSI E I imps exps).Run (.starting s t)
      ((callEvs (E := sigN imps.length) cs).map .inl ++ ansInst (.fail ()) :: rest) z →
    ∃ c' : E.Config Nat, StartRunI E imps (s, t) cs c' ∧
      E.status c'.1 c'.2 = .returned .trap
  | [], s, t, rest, z, h => by
    simp only [callEvs, List.map_nil, List.nil_append] at h
    rcases run_cases h with ⟨hl, -⟩ | ⟨y, hs, hr⟩ | ⟨o, l', y, hl, hs, -⟩
    · cases hl
    · cases hs with
      | sdone run final =>
        rcases run_readying_inv hr with hl | ⟨rest', hl, -⟩
        · cases hl
        · exact (ansInst_ne_fail (List.cons.inj hl).1.symm).elim
      | strap run final => exact ⟨_, .nil run, final⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hs
  | ⟨m, n⟩ :: cs, s, t, rest, z, h => by
    simp only [callEvs, List.map_cons, List.cons_append] at h
    rcases run_cases h with ⟨hl, -⟩ | ⟨y, hs, hr⟩ | ⟨o, l', y, hl, hs, hr⟩
    · cases hl
    · cases hs with
      | sdone run final =>
        rcases run_readying_inv hr with hl | ⟨rest', hl, -⟩
        · cases hl
        · cases (List.cons.inj hl).1
      | strap run final =>
        rcases run_failing_inv hr with hl | ⟨rest', hl⟩
        · cases hl
        · cases (List.cons.inj hl).1
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hs with
      | scall run callout hh =>
        rcases run_cases hr with ⟨hl, -⟩ | ⟨y', hs', -⟩ | ⟨o', l'', y', hl', hs', hr'⟩
        · cases hl
        · cases hs'
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hl'
          cases hs' with
          | sret r =>
            obtain ⟨c', hrun, hf⟩ := run_starting_inv_fail cs hr'
            exact ⟨c', .call run callout hh n hrun, hf⟩

/-- **An instantiation play of an engine instance is `EngineInst`.** -/
theorem engine_inst_inv {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {a : InstAns Unit}
    (h : instPlay (F := sigN exps.length) cs a ∈ engineStrategyI E I imps exps) :
    EngineInst E I imps cs a := by
  have he : instPlay (F := sigN exps.length) cs a =
      (askInst :: (callEvs (E := sigN imps.length) cs).map .inl) ++ [ansInst a] := by
    rw [instPlay_eq]
    simp only [instRound, Round.moves, List.cons_append]
    rfl
  rw [he] at h
  obtain ⟨z, hz⟩ := trace_of_mem_ofLTS h (by simp [ansInst, Move.IsP])
  simp only [List.cons_append] at hz
  obtain ⟨y, hy, hr⟩ := run_fresh_inv hz
  cases hy with
  | @start J f hI hf =>
    rcases a with _ | r
    · obtain ⟨c', ys, hrun, hst, -⟩ := run_starting_inv cs (rest := []) hr
      exact ⟨J, hI, .inr ⟨f, c', ys, hf, hrun, hst⟩⟩
    · cases r
      obtain ⟨c', hrun, hst⟩ := run_starting_inv_fail cs (rest := []) hr
      exact .inr ⟨J, f, c', hI, hf, hrun, hst⟩
  | @noStart J hI hf =>
    rcases run_readying_inv hr with hl | ⟨rest, hl, -⟩
    · cases cs <;> simp at hl
    · rcases cs with _ | ⟨c, cs⟩
      · simp only [callEvs, List.map_nil, List.nil_append, List.cons.injEq] at hl
        obtain ⟨hl, -⟩ := hl
        rcases a with _ | r
        · exact ⟨J, hI, .inl ⟨hf, rfl⟩⟩
        · cases hl
      · cases hl
  | noInst hI =>
    rcases run_failing_inv hr with hl | ⟨rest, hl⟩
    · cases cs <;> simp at hl
    · rcases cs with _ | ⟨c, cs⟩
      · simp only [callEvs, List.map_nil, List.nil_append, List.cons.injEq] at hl
        obtain ⟨hl, -⟩ := hl
        rcases a with _ | r
        · cases hl
        · exact .inl ⟨hI, rfl⟩
      · cases hl

/-- **A failing instantiation without calls fails at one node**: the nodes before it are ready
and that node fails, each without a call. -/
theorem nodesInst_fail_nil {C : CoreSemI M} {n : Nat} :
    ∀ {ps : List (M × List Impl)} {w : List (Call sigU)} {a : InstAns Unit},
      NodesInst C n ps w a → w = [] →
      (a = .ready → ∀ p ∈ ps, instPlay (F := sigU) [] .ready ∈ coreNodeI C n p.1 p.2) ∧
      (a = .fail () → ∃ k, ∃ hk : k < ps.length,
        (∀ j (hj : j < k), instPlay (F := sigU) [] .ready ∈
          coreNodeI C n (ps[j]'(by omega)).1 (ps[j]'(by omega)).2) ∧
        instPlay (F := sigU) [] (.fail ()) ∈ coreNodeI C n ps[k].1 ps[k].2)
  := by
  intro ps w a h
  induction h with
  | nil => exact fun _ => ⟨fun _ _ h => (nomatch h), fun h => (nomatch h)⟩
  | @failed pre x w₁ r h ih =>
    intro hw
    obtain ⟨-, ih⟩ := ih hw
    refine ⟨fun h => (nomatch h), fun hr => ?_⟩
    obtain ⟨k, hk, hb, hf⟩ := ih hr
    refine ⟨k, by simp only [List.length_append]; omega, fun j hj => ?_, ?_⟩
    · have := hb j hj
      simpa only [List.getElem_append_left (show j < pre.length by omega)] using this
    · simpa only [List.getElem_append_left hk] using hf
  | @step pre x w₁ w₂ a h hx ih =>
    intro hw
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hw
    obtain ⟨ih, -⟩ := ih rfl
    have hpre := ih rfl
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · subst ha
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hpre p hp
      · rw [List.mem_singleton] at hp; subst hp; exact hx
    · subst ha
      refine ⟨pre.length, by simp, fun j hj => ?_, ?_⟩
      · simpa only [List.getElem_append_left hj] using hpre _ (List.getElem_mem hj)
      · simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero] using hx

theorem runs_nil_eq {E : Sig.{0}} {A : Type} {P : Prog E A} {a : A} (h : Prog.Runs P [] a) :
    P = .pure a := by
  cases h; rfl

theorem allCalls_eq_nil {E F : Sig.{0}} : ∀ {ys : List (Round E F)}, allCalls ys = [] →
    ∀ y ∈ ys, y.cs = []
  | [], _ => fun _ h => nomatch h
  | y :: ys, h => by
    obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.1 h
    intro y' hy'
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact h₁
    · exact allCalls_eq_nil h₂ y' hy'

/-- **A node's instantiation without calls, at an engine semantics**: its engine instance
instantiates (`EngineInst`) with import calls each answered at once by the wiring. -/
theorem coreNodeI_engine_nil {E : Engine} {emb : M → E.Module} {n : Nat} {m : M}
    {args : List Impl} {a : InstAns Unit}
    (h : instPlay (F := sigU) [] a ∈ coreNodeI (engineSemI E M emb) n m args) :
    ∃ ys : List (Σ _ : (sigN (CoreModule.imports m).length).Op, Option Payload),
      EngineInst E (instOfI E (emb m) (CoreModule.imports m) (CoreModule.exports m))
        (CoreModule.imports m) ys a ∧
      ∀ y ∈ ys, implsN n args (CoreModule.imports m).length y.1 = .pure y.2 := by
  rw [instPlay_eq] at h
  obtain ⟨ys, hm, hr, hw⟩ := coreNodeI_inst_inv h
  have hnil := allCalls_eq_nil hw.symm
  refine ⟨ys.map Round.call, engine_inst_inv (by rw [instPlay_eq]; exact hm), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  have := hr y' hy'
  rw [hnil y' hy'] at this
  exact runs_nil_eq this

end Silmaril.Proofs.Wasm.Component.InstSem
