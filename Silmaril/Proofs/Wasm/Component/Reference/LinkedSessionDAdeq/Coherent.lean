module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Linked
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# The exporter's served rounds along one run, at deterministic profiles

The exporter's side of `Linked2.Chatter` is one run of the exporter's instance threading its
store through infinitely many served rounds (`ExpRunT` for every call of the stream). An infinite
play of the exporter's environment only says that every finite prefix of the served rounds is
served from the instance's store along *some* run; the stores of these runs need not extend one
another (`StratThread.not_coherent`). At a deterministic profile `profile o` they do:

* `expRunT_functional`: the store an `ExpRunT` reaches is a function of the store it starts at and
  of the calls (host-free runs reach at most one normal form, `reach_normal_unique`);
* `exists_expRunT_stream`: if every finite prefix of a stream of call lists is served from `π₀`,
  then one store sequence serves the whole stream;
* `exp_plays_stream`: the same read back from the exporter's environment: if the plays
  `twos` of typed served rounds after `ds₀`, then any number of the call lists `ds k`, are plays
  of the exporter's environment, then the exporter's instance serves `ds₀` and then every `ds k`
  along one run.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-- **The exporter's run is determined** at a deterministic profile. -/
theorem expRunT_functional {o : GrowOracle} {l : Linked2} {I : SInst} {s s₁ s₂ : Store Nat}
    {ds : List (Round (sigN l.imp.imports.length))}
    (h₁ : Linked2.ExpRunT (profile o) l I s ds s₁) (h₂ : Linked2.ExpRunT (profile o) l I s ds s₂) :
    s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | nil => cases h₂; rfl
  | ret w hw hr _ ih =>
    cases h₂ with
    | ret w' hw' hr' h₂' =>
      have hww : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      subst hww
      obtain ⟨t, cvs, ys, run, fin, -, -⟩ := hr.run
      obtain ⟨t', cvs', ys', run', fin', -, -⟩ := hr'.run
      have e := Silmaril.Wasm.Game.reach_normal_unique run run'
        (Silmaril.Wasm.Game.resultAt_no_internal fin)
        (Silmaril.Wasm.Game.resultAt_no_internal fin')
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact ih h₂'
  | trap w hw hr _ ih =>
    cases h₂ with
    | trap w' hw' hr' h₂' =>
      have hww : w = w' := Fin.ext (Option.some.inj (hw.symm.trans hw'))
      subst hww
      obtain ⟨t, res, run, fin, -⟩ := hr.run
      obtain ⟨t', res', run', fin', -⟩ := hr'.run
      have e := Silmaril.Wasm.Game.reach_normal_unique run run'
        (Silmaril.Wasm.Game.resultAt_no_internal fin)
        (Silmaril.Wasm.Game.resultAt_no_internal fin')
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact ih h₂'

theorem expRunT_nil_inv {P : Silmaril.Wasm.Numerics.Profile} {l : Linked2} {I : SInst}
    {s s' : Store Nat} (h : Linked2.ExpRunT P l I s [] s') : s' = s := by
  cases h
  rfl

theorem streamTake_snoc {α : Type} (ω : ℕ → α) (n : ℕ) :
    streamTake ω (n + 1) = streamTake ω n ++ [ω n] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

/-- **One run for a whole stream of calls** at a deterministic profile: if every finite prefix
of the call lists `ds` is served from `π₀`, one store sequence serves them all. -/
theorem exists_expRunT_stream {o : GrowOracle} {l : Linked2} {I : SInst} {π₀ : Store Nat}
    (ds : ℕ → List (Round (sigN l.imp.imports.length)))
    (h : ∀ n, ∃ π, Linked2.ExpRunT (profile o) l I π₀ (streamTake ds n).flatten π) :
    ∃ st : ℕ → Store Nat, st 0 = π₀ ∧
      ∀ k, Linked2.ExpRunT (profile o) l I (st k) (ds k) (st (k + 1)) := by
  choose st hst using h
  refine ⟨st, ?_, fun k => ?_⟩
  · have h₀ := hst 0
    simp only [streamTake, List.ofFn_zero, List.flatten_nil] at h₀
    exact expRunT_nil_inv h₀
  · have h₁ := hst (k + 1)
    rw [streamTake_snoc, List.flatten_append, List.flatten_singleton] at h₁
    obtain ⟨π, ha, hb⟩ := expRunT_split _ _ h₁
    obtain rfl := expRunT_functional ha (hst k)
    exact hb

/-- **The exporter's environment, serving typed rounds forever, read back along one run** (at a
deterministic profile, under `Linked2.Adequate`): if the plays of the served rounds of `ds₀` and
then of any number of the call lists `ds k` are plays of the exporter's environment, then the
exporter's instance serves `ds₀` from its store, and then every `ds k`, along one run. -/
theorem exp_plays_stream {o : GrowOracle} {l : Linked2} (hl : l.Adequate) {Ie : SInst}
    (hIe : l.exp.mod.IsInst Ie) (ds₀ : List (Round (sigN l.imp.imports.length)))
    (ds : ℕ → List (Round (sigN l.imp.imports.length))) (hwt₀ : ∀ y ∈ ds₀, WT l y)
    (hwt : ∀ k, ∀ y ∈ ds k, WT l y)
    (h : ∀ n, (twos ((ds₀ ++ (streamTake ds n).flatten).map (wireRound l)) :
      List (Move sigU sigU)) ∈ (Linked2.expObs (impSemD (profile o)) l).plays) :
    ∃ st : ℕ → Store Nat, Linked2.ExpRunT (profile o) l Ie Ie.store ds₀ (st 0) ∧
      ∀ k, Linked2.ExpRunT (profile o) l Ie (st k) (ds k) (st (k + 1)) := by
  have hrun : ∀ n, ∃ π, Linked2.ExpRunT (profile o) l Ie Ie.store
      (ds₀ ++ (streamTake ds n).flatten) π := by
    intro n
    have hWT : ∀ y ∈ ds₀ ++ (streamTake ds n).flatten, WT l y := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hwt₀ y hy
      · obtain ⟨d, hd, hy⟩ := List.mem_flatten.mp hy
        simp only [streamTake, List.mem_ofFn] at hd
        obtain ⟨i, rfl⟩ := hd
        exact hwt i y hy
    have hn := h n
    rw [expObs_plays] at hn
    have hspec := expEnv_specRoundsT hl.expGood hIe hn
    obtain ⟨π, hS⟩ := sessRounds_of_specRoundsT hspec fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨w, ws, hw, -, -⟩ := hWT y hy
      show (l.wire.getD y.1.1.val 0) < _
      rw [wire_getD hw]
      exact w.isLt
    exact ⟨π, expRunT_of_sessRounds _ hWT hS⟩
  obtain ⟨π₁, h₀, -⟩ := expRunT_split _ _ (hrun 0).choose_spec
  obtain ⟨st, hst0, hst⟩ := exists_expRunT_stream (π₀ := π₁) ds fun n => by
    obtain ⟨π, hπ⟩ := hrun n
    obtain ⟨π', ha, hb⟩ := expRunT_split _ _ hπ
    obtain rfl := expRunT_functional ha h₀
    exact ⟨π, hb⟩
  exact ⟨st, hst0 ▸ h₀, hst⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
