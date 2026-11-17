module

public import Silmaril.Sim.RV64.Reduce.Defs
public import Silmaril.Sim.RV64.Mem.Thms

/-!
# Reducing RV64 problems to Wasm problems: the transfer theorem

* `TSafe.exists_exit`: a totally correct configuration has a run to an exit;
* `step_run`: every call of `step` has a run that returns, and the result satisfies `StepPost`
  (from the total `step_sound`);
* **`reduce`**: a solution of the Wasm problem `WasmRun … I n` (partial-correctness triples
  about the concrete module), from memory bytes `B` with `I 0 B`, gives the RV64 fact
  `Halts (absCode B) (absState B) n (absState B')` for some `B'` with `I n B'`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Reduce

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Words (MemAt SameOutside)
open Silmaril.Wasm.Logic.Hoare (TSafe TFSpecAt FSpecValid Exits callPost)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem TSafe.exists_exit {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hp _ ih =>
    obtain ⟨c₁, h₁⟩ := hp
    obtain ⟨c', hs, o, he, hq⟩ := ih c₁ h₁
    exact ⟨c', .head h₁ hs, o, he, hq⟩

theorem refRun_succ_right (code : Code) :
    ∀ (j : Nat) (σ : Silmaril.RiscV.State),
      refRun code (j + 1) σ = (refRun code j σ).bind (refStep code)
  | 0, σ => by
    show (refStep code σ).bind (refRun code 0) = refStep code σ
    cases refStep code σ <;> rfl
  | j + 1, σ => by
    show (refStep code σ).bind (refRun code (j + 1)) =
      ((refStep code σ).bind (refRun code j)).bind (refStep code)
    cases refStep code σ <;> simp [refRun_succ_right code j]

section
variable {fi : FuncInst H} {a ma : Nat} {mt : MemoryType}
  {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}

/-- **A call of `step` returns**, with a result satisfying `StepPost`. -/
theorem step_run (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) {s : Store H} {B : ByteArray} (hf : s.funcs[a]? = some fi)
    (hm : MemAt s fi.module ma mt B) (hB : WF B) :
    ∃ (st : BitVec 32) (B' : ByteArray) (f' : Frame),
      Steps P host (invoke s a []) ⟨s.setMem ma ⟨mt, B'⟩, f', vals [.num ⟨.int .i32, st⟩]⟩ ∧
      StepPost B st B' := by
  have hT := step_sound (P := P) (host := host) (a := a) (ma := ma) (mt := mt) (B := B) hcode he hps
    hrs s [] ⟨hf, rfl, hm, hB⟩ {} []
    (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial
  obtain ⟨⟨s', f', c'⟩, hs, o, hex, hcp⟩ := TSafe.exists_exit hT
  obtain ⟨-, hcp⟩ := hcp
  rcases hcp with ⟨res, rfl, st, B', ho, rfl, hp⟩ | ⟨rfl, st, B', ho, -⟩ | ⟨_, rfl, st, B', ho, -⟩
  · simp only [Outcome.normal.injEq] at ho
    subst ho
    have hc : c' = vals [.num ⟨.int .i32, st⟩] := hex
    subst hc
    exact ⟨st, B', f', by simpa [Silmaril.Wasm.Logic.Hoare.invoke_code] using hs, hp⟩
  · cases ho
  · cases ho

/-- One call: the run of `step_run` also satisfies a user triple for the same store. -/
theorem step_triple (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) {Pre : ByteArray → Prop} {Post : BitVec 32 → ByteArray → Prop}
    (hU : FSpecValid P host a (tripleSpec fi a ma mt Pre Post)) {s : Store H} {B : ByteArray}
    (hf : s.funcs[a]? = some fi) (hm : MemAt s fi.module ma mt B) (hB : WF B) (hpre : Pre B) :
    ∃ (st : BitVec 32) (B' : ByteArray), StepPost B st B' ∧ Post st B' ∧
      MemAt (s.setMem ma ⟨mt, B'⟩) fi.module ma mt B' := by
  obtain ⟨st, B', f', hs, hp⟩ := step_run (P := P) (host := host) hcode he hps hrs hf hm hB
  obtain ⟨st', B'', ho, hm', hq⟩ := FSpecValid.invoke_vals hU ⟨hf, rfl, B, hm, hpre⟩ hs
  simp only [Outcome.normal.injEq, List.cons.injEq, and_true] at ho
  cases ho
  have hm2 : MemAt (s.setMem ma ⟨mt, B'⟩) fi.module ma mt B' := hm.setMem B'
  obtain ⟨-, -, rfl⟩ := hm2.unique hm'
  exact ⟨st, B'', hp, hq, hm2⟩

/-- One more call of `step` extends the run invariant of `reduce` by one reference step. -/
private theorem reduce_succ (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) {I : Nat → ByteArray → Prop} {j : Nat}
    (hU : FSpecValid P host a (tripleSpec fi a ma mt (I j) fun st B' => st = 0 ∧ I (j + 1) B'))
    {B B' : ByteArray} {s' : Store H} (hf' : s'.funcs[a]? = some fi)
    (hm' : MemAt s' fi.module ma mt B') (hB' : WF B') (hI : I j B') (hc : absCode B' = absCode B)
    (hr : refRun (absCode B) j (absState B) = some (absState B')) :
    ∃ (s'' : Store H) (B'' : ByteArray), s''.funcs[a]? = some fi ∧
      MemAt s'' fi.module ma mt B'' ∧ WF B'' ∧ I (j + 1) B'' ∧ absCode B'' = absCode B ∧
      refRun (absCode B) (j + 1) (absState B) = some (absState B'') := by
  obtain ⟨st, B'', hp, hpost, hm''⟩ : ∃ (st : BitVec 32) (B'' : ByteArray), StepPost B' st B'' ∧
      (st = 0 ∧ I (j + 1) B'') ∧ MemAt (s'.setMem ma ⟨mt, B''⟩) fi.module ma mt B'' :=
    step_triple (P := P) (host := host) hcode he hps hrs hU hf' hm' hB' hI
  have hret : refStep (absCode B') (absState B') = some (absState B'') ∧
      SameOutside B' B'' 0 256 := by
    rcases hp with ⟨-, hstep, hso⟩ | ⟨hst, -, -⟩
    · exact ⟨hstep, hso⟩
    · exact absurd hpost.1 (by rcases hst with h | h <;> simp [h])
  have hf'' : (s'.setMem ma ⟨mt, B''⟩).funcs[a]? = some fi := by
    simpa only [Store.setMem] using hf'
  have hrun : refRun (absCode B) (j + 1) (absState B) = some (absState B'') := by
    rw [refRun_succ_right, hr, ← hc]
    exact hret.1
  exact ⟨_, B'', hf'', hm'', wf_of_sameOutside hret.2 hB', hpost.2,
    (absCode_of_sameOutside hret.2).trans hc, hrun⟩

/-- **The transfer theorem** (RV64 problem ⇐ Wasm problem). If the Wasm problem
`WasmRun P host fi a ma mt I n` is solved, then from every store holding `step` at `a` and
memory bytes `B` with `I 0 B`, the reference RV64 machine with the code and state held by `B`
halts after exactly `n` steps, in the state held by some `B'` with `I n B'`. -/
theorem reduce (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) {I : Nat → ByteArray → Prop} {n : Nat}
    (hW : WasmRun P host fi a ma mt I n) {s : Store H} {B : ByteArray}
    (hf : s.funcs[a]? = some fi) (hm : MemAt s fi.module ma mt B) (hB : WF B) (h0 : I 0 B) :
    ∃ B', I n B' ∧ Halts (absCode B) (absState B) n (absState B') := by
  -- the first `j` calls retire `j` reference steps
  have hrun : ∀ j ≤ n, ∃ (s' : Store H) (B' : ByteArray), s'.funcs[a]? = some fi ∧
      MemAt s' fi.module ma mt B' ∧ WF B' ∧ I j B' ∧ absCode B' = absCode B ∧
      refRun (absCode B) j (absState B) = some (absState B') := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨s, B, hf, hm, hB, h0, rfl, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨s', B', hf', hm', hB', hI, hc, hr⟩ := ih (by omega)
      exact reduce_succ hcode he hps hrs (hW.1 j (by omega)) hf' hm' hB' hI hc hr
  obtain ⟨s', B', hf', hm', hB', hI, hc, hr⟩ := hrun n le_rfl
  obtain ⟨st, B'', hp, hne, -⟩ : ∃ (st : BitVec 32) (B'' : ByteArray), StepPost B' st B'' ∧
      st ≠ 0 ∧ MemAt (s'.setMem ma ⟨mt, B''⟩) fi.module ma mt B'' :=
    step_triple (P := P) (host := host) hcode he hps hrs hW.2 hf' hm' hB' hI
  have hstop : refStep (absCode B) (absState B') = none := by
    rw [← hc]
    rcases hp with ⟨h0', -, -⟩ | ⟨-, -, hstop⟩
    · exact absurd h0' hne
    · exact hstop
  exact ⟨B', hI, hr, hstop⟩

end

end Silmaril.Sim.RV64.Reduce
