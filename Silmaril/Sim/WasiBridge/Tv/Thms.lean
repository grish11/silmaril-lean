module

public import Silmaril.Sim.WasiBridge.Tv.Defs
public import Silmaril.Sim.WasiBridge.Cli.Thms

/-!
# Translation validation of CLI binaries (theorems)

PROVED (standard axioms):

* runs: `Run.trans`, `Run.single`;
* certificates: `WSim.run`, `WSim.refines` (a simulation is trace refinement), `WSim.refl`,
  `WSim.comp`; **`Cert.equiv`** (a TV certificate is trace equivalence), `Cert.refl`,
  `Cert.symm`, `Cert.trans`; **`Slice.cert`** (a slice is a certificate);
* ended traces: `EndedEquiv.of_equiv`, `ElfWasiEquiv.ended`, `traceModel_ended`,
  `traceModel_eq_of_ended`, **`sat_iff_of_elfWasiEnded`**, `native_sat_of_wasi_ended` (the
  ended-trace forms of `sat_iff_of_elfWasiEquiv` and `native_sat_of_wasi`);
* **`sat_iff_of_cert`**: certified families of transition systems satisfy the same `L1`
  sentences; `elfWasiEnded_of_cert`: a certificate between a process and an operational
  model of a WASI program gives `ElfWasiEnded`;
* processes: **`procLts_traces`** (the transition system of a process has its `procObs`
  traces); **`procObs_eq_of_agree`** and **`procObs_restrict`** (instruction slicing: a step
  that agrees with the full one on the reachable states, e.g. a simulator restricted to the
  instructions a binary uses, has the same observable traces);
* hello: `writeLoop_ended` (the ended traces of the write-loop simulator), `writeLoop_prints`,
  **`writeLoop_hello`** (the write-loop simulator is ended-equivalent to the preview1 `hello`),
  **`helloLoop_ended`** (given `Task.helloLoopEnds`, every proved x86 `hello` runtime is
  ended-equivalent to the preview1 `hello`, so its CLI model *is* the WASI program's:
  `helloLoop_model_eq`), `helloLoopEnds_of_slice` (the slice route).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Tv

open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.X86 (MState)
open Silmaril.Process.LPS.Machines
open Silmaril.Cli (Bytes)
open Silmaril.Cli.Institution (Level Model Sen Out1)

/-! ## Runs -/

theorem Lts.Run.trans {A : Lts} {s s' s'' : A.St} {t u : List Obs} (h : A.Run s t s')
    (h' : A.Run s' u s'') : A.Run s (t ++ u) s'' := by
  induction h with
  | refl => simpa using h'
  | cons hs _ ih => simpa [List.append_assoc] using Lts.Run.cons hs (ih h')

theorem Lts.Run.single {A : Lts} {s s' : A.St} {w : List Obs} (h : A.step s w s') :
    A.Run s w s' := by
  simpa using Lts.Run.cons h (Lts.Run.refl s')

/-! ## Simulations and certificates -/

theorem WSim.run {A B : Lts} (f : WSim A B) {s s' : A.St} {w : List Obs} (h : A.Run s w s') :
    ∀ {t}, f.R s t → ∃ t', B.Run t w t' ∧ f.R s' t' := by
  induction h with
  | refl s => exact fun hr => ⟨_, .refl _, hr⟩
  | cons hs _ ih =>
    intro t hr
    obtain ⟨t₁, hr₁, h₁⟩ := f.step hr hs
    obtain ⟨t₂, hr₂, h₂⟩ := ih h₁
    exact ⟨t₂, hr₁.trans hr₂, h₂⟩

/-- **A simulation is trace refinement.** -/
theorem WSim.refines {A B : Lts} (f : WSim A B) : Refines A.traces B.traces := by
  rintro t ⟨s, hs⟩
  obtain ⟨t', h, -⟩ := f.run hs f.init
  exact ⟨t', h⟩

/-- The identity simulation. -/
def WSim.refl (A : Lts) : WSim A A :=
  ⟨Eq, rfl, fun {_ _ _ s'} hr hs => ⟨s', hr ▸ Lts.Run.single hs, rfl⟩⟩

/-- Simulations compose. -/
def WSim.comp {A B C : Lts} (f : WSim A B) (g : WSim B C) : WSim A C where
  R s u := ∃ t, f.R s t ∧ g.R t u
  init := ⟨B.init, f.init, g.init⟩
  step := by
    rintro s u w s' ⟨t, hf, hg⟩ hs
    obtain ⟨t', hr, hf'⟩ := f.step hf hs
    obtain ⟨u', hr', hg'⟩ := g.run hr hg
    exact ⟨u', hr', t', hf', hg'⟩

/-- **A TV certificate is trace equivalence.** -/
theorem Cert.equiv {A B : Lts} (c : Cert A B) : Equiv A.traces B.traces :=
  ⟨c.fwd.refines, c.bwd.refines⟩

def Cert.refl (A : Lts) : Cert A A := ⟨WSim.refl A, WSim.refl A⟩

def Cert.symm {A B : Lts} (c : Cert A B) : Cert B A := ⟨c.bwd, c.fwd⟩

def Cert.trans {A B C : Lts} (c : Cert A B) (d : Cert B C) : Cert A C :=
  ⟨c.fwd.comp d.fwd, d.bwd.comp c.bwd⟩

/-- **A slice is a certificate**: the sliced simulator has the traces of the full one. -/
def Slice.cert {A B : Lts} (σ : Slice A B) : Cert A B where
  fwd :=
    { R := fun s b => σ.Inv s ∧ σ.abs s = b
      init := ⟨σ.init_inv, σ.init_abs⟩
      step := by
        rintro s b w s' ⟨hi, rfl⟩ hs
        obtain ⟨hi', hr⟩ := σ.fwd hi hs
        exact ⟨_, hr, hi', rfl⟩ }
  bwd :=
    { R := fun b s => σ.Inv s ∧ σ.abs s = b
      init := ⟨σ.init_inv, σ.init_abs⟩
      step := by
        rintro b s w b' ⟨hi, rfl⟩ hs
        obtain ⟨s', hr, hi', ha⟩ := σ.bwd hi hs
        exact ⟨s', hr, hi', ha⟩ }

/-! ## Ended traces -/

theorem EndedEquiv.of_equiv {P Q : List Obs → Prop} (h : Equiv P Q) : EndedEquiv P Q :=
  ⟨fun t ⟨hp, he⟩ => ⟨h.1 t hp, he⟩, fun t ⟨hq, he⟩ => ⟨h.2 t hq, he⟩⟩

theorem EndedEquiv.trans {P Q R : List Obs → Prop} (h : EndedEquiv P Q) (h' : EndedEquiv Q R) :
    EndedEquiv P R :=
  Equiv.trans h h'

theorem EndedEquiv.symm {P Q : List Obs → Prop} (h : EndedEquiv P Q) : EndedEquiv Q P :=
  Equiv.symm h

/-- `ElfWasiEquiv` implies its ended-trace form. -/
theorem ElfWasiEquiv.ended {P : List Obs → Prop} {W : P1Sem} {S : Subset}
    (h : ElfWasiEquiv P W S) : ElfWasiEnded P W S :=
  EndedEquiv.of_equiv h

/-- A CLI observation reads only ended traces. -/
theorem traceModel_ended (P : Bytes → List Obs → Prop) :
    traceModel (fun s => Ended (P s)) = traceModel P := by
  ext s o
  constructor
  · rintro ⟨t, ⟨ht, -⟩, he⟩
    exact ⟨t, ht, he⟩
  · rintro ⟨t, ht, he⟩
    refine ⟨t, ⟨ht, ?_⟩, he⟩
    cases h : endCode t <;> simp_all [out1]

theorem traceModel_eq_of_ended {P Q : Bytes → List Obs → Prop}
    (h : ∀ s, EndedEquiv (P s) (Q s)) : traceModel P = traceModel Q := by
  rw [← traceModel_ended P, ← traceModel_ended Q, traceModel_eq h]

/-- **Ended-trace equivalence to a WASI program transfers CLI satisfaction, both ways.** -/
theorem sat_iff_of_elfWasiEnded {P : Bytes → List Obs → Prop} {W : Bytes → P1Sem} {S : Subset}
    (h : ∀ s, ElfWasiEnded (P s) (W s) S) (φ : Sen Level.stream.sig) :
    (traceModel P).Sat φ ↔ (p1Model W S).Sat φ := by
  rw [p1Model, traceModel_eq_of_ended h]

/-- `native_sat_of_wasi` with ended-trace equivalence. -/
theorem native_sat_of_wasi_ended {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    {W : Bytes → P1Sem} {S : Subset} {φ : Sen Level.stream.sig}
    (hW : (p1Model W S).Sat φ) (hE : ∀ s, ElfWasiEnded (P s) (W s) S)
    (hT : Task.nativeInTraces M P) : M.Sat (Level.lift φ) :=
  (Level.sat_lift_iff M φ).mpr (((sat_iff_of_elfWasiEnded hE φ).mpr hW).anti hT)

/-- **Certified families satisfy the same `L1` sentences.** -/
theorem sat_iff_of_cert {A B : Bytes → Lts} (c : ∀ s, Cert (A s) (B s)) (φ : Sen Level.stream.sig) :
    (traceModel fun s => (A s).traces).Sat φ ↔ (traceModel fun s => (B s).traces).Sat φ := by
  rw [traceModel_eq fun s => (c s).equiv]

/-- **TV to WASI**: a certificate between a transition system and an operational model `B` of a
WASI program (ended-equivalent to its trace semantics) gives ended equivalence. -/
theorem elfWasiEnded_of_cert {A B : Lts} {W : P1Sem} {S : Subset} (c : Cert A B)
    (hB : EndedEquiv B.traces (W.obs S)) : ElfWasiEnded A.traces W S :=
  (EndedEquiv.of_equiv c.equiv).trans hB

/-! ## Processes -/

theorem procLts_run_none {step : MState → Option MState} {E : SysEnv} {m : MState} {e : E.Model}
    {t : List Obs} {y : (procLts step E m e).St} (h : (procLts step E m e).Run none t y) : t = [] := by
  match h with
  | .refl _ => rfl
  | .cons hs _ => nomatch hs

theorem procLts_run_procRun {step : MState → Option MState} {E : SysEnv} {m₀ : MState}
    {e₀ : E.Model} {x y : (procLts step E m₀ e₀).St} {t : List Obs} (h : (procLts step E m₀ e₀).Run x t y) :
    ∀ {m e}, x = some (m, e) → procObs step E m e t := by
  induction h with
  | refl => rintro m e -; exact ⟨[], .stop m e, rfl⟩
  | @cons s s' s'' w t hs hr ih =>
    rintro m e rfl
    cases hs with
    | user hm =>
      obtain ⟨tr, h, rfl⟩ := ih rfl
      exact ⟨tr, .step hm h, by simp⟩
    | resume ha harm =>
      obtain ⟨tr, h, rfl⟩ := ih rfl
      exact ⟨_, .resume ha harm h, by simp [obsTrace]⟩
    | halt ha harm =>
      rw [procLts_run_none hr]
      exact ⟨_, .halt ha harm, by simp⟩

theorem procRun_procLts_run {step : MState → Option MState} {E : SysEnv} {m₀ : MState}
    {e₀ : E.Model} {m : MState} {e : E.Model} {tr : List Silmaril.Process.LPS.Event}
    (h : ProcRun step E m e tr) : ∃ y, (procLts step E m₀ e₀).Run (some (m, e)) (obsTrace tr) y := by
  induction h with
  | stop m e => exact ⟨_, .refl _⟩
  | step hm _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨y, by simpa using Lts.Run.cons (ProcStep.user hm) hy⟩
  | resume ha harm _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨y, by simpa [obsTrace] using Lts.Run.cons (ProcStep.resume ha harm) hy⟩
  | halt ha harm => exact ⟨_, Lts.Run.single (ProcStep.halt ha harm)⟩

/-- **The transition system of a process has the process's observable traces.** -/
theorem procLts_traces (step : MState → Option MState) (E : SysEnv) (m : MState) (e : E.Model) :
    (procLts step E m e).traces = procObs step E m e := by
  funext t
  apply propext
  constructor
  · rintro ⟨y, h⟩
    exact procLts_run_procRun h rfl
  · rintro ⟨tr, h, rfl⟩
    exact procRun_procLts_run h

/-- Runs carry over to a step that agrees on an invariant closed under steps and answers. -/
theorem procRun_of_agree {step step' : MState → Option MState} {E : SysEnv}
    {Inv : MState → E.Model → Prop}
    (hag : ∀ m e, Inv m e → step' m = step m)
    (hstep : ∀ m e m', Inv m e → step m = some m' → Inv m' e)
    (hres : ∀ m e m' e' ch evs, Inv m e → AtSyscall m →
      E.arm (trapped ⟨m, none⟩ ch) e (.resume m' e' evs) → Inv m' e')
    {m : MState} {e : E.Model} {tr : List Silmaril.Process.LPS.Event}
    (h : ProcRun step E m e tr) (hi : Inv m e) : ProcRun step' E m e tr := by
  induction h with
  | stop => exact .stop _ _
  | step hm _ ih => exact .step ((hag _ _ hi).trans hm) (ih (hstep _ _ _ hi hm))
  | resume ha harm _ ih => exact .resume ha harm (ih (hres _ _ _ _ _ _ hi ha harm))
  | halt ha harm => exact .halt ha harm

/-- **Instruction slicing**: a user step that agrees with the full one on an invariant of the
process (closed under its steps and the environment's answers) has the same observable traces.
-/
theorem procObs_eq_of_agree {step step' : MState → Option MState} {E : SysEnv}
    {Inv : MState → E.Model → Prop}
    (hag : ∀ m e, Inv m e → step' m = step m)
    (hstep : ∀ m e m', Inv m e → step m = some m' → Inv m' e)
    (hres : ∀ m e m' e' ch evs, Inv m e → AtSyscall m →
      E.arm (trapped ⟨m, none⟩ ch) e (.resume m' e' evs) → Inv m' e')
    {m : MState} {e : E.Model} (hi : Inv m e) :
    procObs step' E m e = procObs step E m e := by
  funext t
  apply propext
  constructor
  · rintro ⟨tr, h, rfl⟩
    refine ⟨tr, procRun_of_agree (step := step') (fun m e hi => (hag m e hi).symm) ?_ hres h hi, rfl⟩
    intro m e m' hi hm
    exact hstep m e m' hi ((hag m e hi) ▸ hm)
  · rintro ⟨tr, h, rfl⟩
    exact ⟨tr, procRun_of_agree hag hstep hres h hi, rfl⟩

/-- **A simulator restricted to the instructions a binary uses** has the binary's observable
traces, when every reachable state is accepted (`Ok`). -/
theorem procObs_restrict {Ok : MState → Prop} [DecidablePred Ok] {step : MState → Option MState}
    {E : SysEnv} {Inv : MState → E.Model → Prop}
    (hok : ∀ m e, Inv m e → Ok m)
    (hstep : ∀ m e m', Inv m e → step m = some m' → Inv m' e)
    (hres : ∀ m e m' e' ch evs, Inv m e → AtSyscall m →
      E.arm (trapped ⟨m, none⟩ ch) e (.resume m' e' evs) → Inv m' e')
    {m : MState} {e : E.Model} (hi : Inv m e) :
    procObs (restrictStep Ok step) E m e = procObs step E m e :=
  procObs_eq_of_agree (fun m e hi => by simp [restrictStep, hok m e hi]) hstep hres hi

/-! ## The hello prototype -/

theorem writeLoop_run_none {fd code : Nat} {msg : List (BitVec 8)} {t : List Obs}
    {y : (writeLoop fd msg code).St}
    (h : (writeLoop fd msg code).Run none t y) : t = [] := by
  match h with
  | .refl _ => rfl
  | .cons hs _ => nomatch hs

theorem endCode_map_wr (fd : Nat) (p : List (BitVec 8)) : endCode (p.map (.wr fd)) = none := by
  unfold endCode
  rcases List.eq_nil_or_concat p with rfl | ⟨l, b, rfl⟩ <;> simp

theorem writeLoop_run {fd code : Nat} {msg : List (BitVec 8)} {x y : (writeLoop fd msg code).St}
    {t : List Obs}
    (h : (writeLoop fd msg code).Run x t y) :
    ∀ {r}, x = some r → t = r.map (.wr fd) ++ [.exit code] ∨
      ∃ p r', y = some r' ∧ r = p ++ r' ∧ t = p.map (.wr fd) := by
  induction h with
  | refl => rintro r rfl; exact .inr ⟨[], r, rfl, rfl, rfl⟩
  | @cons s s' s'' w t hs hr ih =>
    rintro r rfl
    cases hs with
    | write r k =>
      rcases ih rfl with h | ⟨p, r', hy, hr', ht⟩
      · left
        rw [h, ← List.append_assoc, ← List.map_append, List.take_append_drop]
      · right
        refine ⟨r.take k ++ p, r', hy, ?_, ?_⟩
        · rw [List.append_assoc, ← hr', List.take_append_drop]
        · rw [ht, List.map_append]
    | exit =>
      left
      rw [writeLoop_run_none hr]
      simp

/-- **The ended traces of the write-loop simulator**: exactly the whole message, then the
exit. -/
theorem writeLoop_ended (fd : Nat) (msg : List (BitVec 8)) (code : Nat) (t : List Obs) :
    Ended (writeLoop fd msg code).traces t ↔ t = msg.map (.wr fd) ++ [.exit code] := by
  constructor
  · rintro ⟨⟨y, h⟩, he⟩
    rcases writeLoop_run h rfl with h | ⟨p, r', -, -, rfl⟩
    · exact h
    · simp [endCode_map_wr] at he
  · rintro rfl
    refine ⟨⟨none, ?_⟩, by simp [endCode]⟩
    have hx : (writeLoop fd msg code).step (some []) [.exit code] none := WriteStep.exit
    have hw : (writeLoop fd msg code).step (some msg) (msg.map (.wr fd)) (some []) := by
      have h := WriteStep.write (fd := fd) (code := code) msg msg.length
      rw [List.take_of_length_le (le_refl _), List.drop_of_length_le (le_refl _)] at h
      exact h
    exact Lts.Run.cons hw (Lts.Run.single hx)

theorem writtenOn_wr (fd : Nat) (msg : List (BitVec 8)) (code : Nat) :
    writtenOn fd (msg.map (.wr fd) ++ [.exit code]) = msg := by
  induction msg with
  | nil => simp [writtenOn]
  | cons b msg ih => simp [writtenOn]

/-- **The write-loop simulator prints its message** (level `L1`, exit `0`). -/
theorem writeLoop_prints (msg : List (BitVec 8)) :
    (traceModel fun _ => (writeLoop 1 msg 0).traces).Sat (Sen.prints (cliBytes msg)) := by
  rw [← traceModel_ended]
  rintro s o ⟨t, ht, he⟩
  rw [writeLoop_ended] at ht
  subst ht
  simp only [out1, endCode, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.map_some, Option.some.injEq] at he
  subst he
  refine ⟨?_, rfl⟩
  simp [writtenOn_wr]

theorem helloObs_eq : helloObs = [0x68, 0x69].map (Obs.wr 1) ++ [Obs.exit 0] := rfl

theorem helloObs_mem : helloP1Sem.obs S1 helloObs :=
  ⟨_, List.prefix_refl _, helloP1_in, helloP1_flat ▸ List.prefix_refl _⟩

/-- The ended traces of the preview1 `hello`. -/
theorem helloP1_ended (t : List Obs) : Ended (helloP1Sem.obs S1) t ↔ t = helloObs := by
  constructor
  · rintro ⟨⟨t', ht, -, hp⟩, he⟩
    exact helloObs_ended (helloP1_flat ▸ hp.trans (flatMap_prefix ht)) he
  · rintro rfl
    exact ⟨helloObs_mem, by simp [endCode, helloObs]⟩

/-- **The write-loop simulator of `hi` is ended-equivalent to the preview1 `hello`.** -/
theorem writeLoop_hello : ElfWasiEnded (writeLoop 1 [0x68, 0x69] 0).traces helloP1Sem S1 := by
  constructor <;> intro t h
  · rw [helloP1_ended, helloObs_eq]; exact (writeLoop_ended _ _ _ t).1 h
  · rw [writeLoop_ended, ← helloObs_eq]; exact (helloP1_ended t).1 h

/-- An ended trace refining the preview1 `hello` is all of it. -/
theorem helloLoop_ended_of {P : List Obs → Prop} (href : Refines P (helloP1Sem.obs S1))
    (hend : ∃ t, P t ∧ (endCode t).isSome) : ElfWasiEnded P helloP1Sem S1 := by
  constructor
  · rintro t ⟨ht, he⟩
    exact ⟨href t ht, he⟩
  · rintro t h
    obtain ⟨t', ht', he'⟩ := hend
    have h₁ : t' = helloObs := (helloP1_ended t').1 ⟨href t' ht', he'⟩
    have h₂ : t = helloObs := (helloP1_ended t).1 h
    exact ⟨h₂ ▸ h₁ ▸ ht', h.2⟩

/-- **Every proved x86 `hello` runtime is ended-equivalent to the preview1 `hello`**, given
progress (`Task.helloLoopEnds`). -/
theorem helloLoop_ended (hT : Task.helloLoopEnds) {c : MState → Option MState}
    {segs : List Silmaril.Process.LPS.Segment} {e : Silmaril.Process.LPS.Model}
    (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e) (hstuck : ∀ m, AtSyscall m → c m = none) :
    ElfWasiEnded (procObs c (lpsEnv segs) R.start e) helloP1Sem S1 :=
  helloLoop_ended_of (helloLoop_refines R hstuck) (hT c segs e R hstuck)

/-- **The CLI model of the x86 `hello` runtime is the WASI program's** (given progress): they
satisfy the same `L1` sentences, in both directions. -/
theorem helloLoop_model_eq (hT : Task.helloLoopEnds) {c : MState → Option MState}
    {segs : List Silmaril.Process.LPS.Segment} {e : Silmaril.Process.LPS.Model}
    (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e) (hstuck : ∀ m, AtSyscall m → c m = none) :
    traceModel (fun _ => procObs c (lpsEnv segs) R.start e) = p1Model (fun _ => helloP1Sem) S1 :=
  traceModel_eq_of_ended fun _ => helloLoop_ended hT R hstuck

/-- **The slice route to progress**: a slice onto the write-loop simulator gives an ended run. -/
theorem helloLoopEnds_of_slice (hS : Task.helloLoopSlice) : Task.helloLoopEnds := by
  intro c segs e R hstuck
  obtain ⟨σ⟩ := hS c segs e R hstuck
  have hw : Ended (writeLoop 1 [0x68, 0x69] 0).traces helloObs :=
    (writeLoop_ended _ _ _ _).2 helloObs_eq
  obtain ⟨⟨y, hr⟩, he⟩ := (EndedEquiv.of_equiv σ.cert.equiv).2 _ hw
  exact ⟨helloObs, procLts_run_procRun hr rfl, he⟩

end Silmaril.Sim.WasiBridge.Tv

/-- info: 'Silmaril.Sim.WasiBridge.Tv.Cert.equiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.Cert.equiv
/-- info: 'Silmaril.Sim.WasiBridge.Tv.sat_iff_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.sat_iff_of_cert
/-- info: 'Silmaril.Sim.WasiBridge.Tv.sat_iff_of_elfWasiEnded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.sat_iff_of_elfWasiEnded
/-- info: 'Silmaril.Sim.WasiBridge.Tv.procLts_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.procLts_traces
/-- info: 'Silmaril.Sim.WasiBridge.Tv.procObs_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.procObs_restrict
/-- info: 'Silmaril.Sim.WasiBridge.Tv.writeLoop_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.writeLoop_hello
/-- info: 'Silmaril.Sim.WasiBridge.Tv.writeLoop_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.writeLoop_prints
/-- info: 'Silmaril.Sim.WasiBridge.Tv.helloLoop_model_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.helloLoop_model_eq
/-- info: 'Silmaril.Sim.WasiBridge.Tv.helloLoopEnds_of_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.helloLoopEnds_of_slice
