module

public import Silmaril.Containers.Lps.Defs
public import Silmaril.Process.LPS.Probes.Oracle
public import Silmaril.Process.LPS.Probes.KitMemory

/-!
# Proofs: probe-kit rules over any system call table, with model changes

Proofs for `Silmaril.Containers.Lps.Thms` (the kit section). The probe kit's flag-oracle rules
(`Probes.Probe.osstep_*`) are stated for LPS's native table and for calls that keep the model.
Here: instruction and trap steps do not consult the table (`sstep_table_irrel`), so they hold
under any table; a returning call may change the model (`osstep_sys_iff`); an exit holds under
any table with the native outcomes (`osstep_halt_iffT`).
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Lps.Kit

open Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-- A configuration with no pending system call steps the same way under every table. -/
theorem sstep_table_irrel {isa : UserIsa} {segs : List Segment} {sp₁ sp₂ : Sys SyscallEffect}
    {refused : RefusalFilter} {c : Silmaril.Process.LPS.Config isa} {evs : List Event}
    {t : StepTo isa} (hn : isa.svcPending c.ms = none) :
    SStep segs sp₁ refused c evs t ↔ SStep segs sp₂ refused c evs t := by
  constructor
  · intro h
    cases h with
    | instr a b c => exact .instr a b c
    | instrFault a b c => exact .instrFault a b c
    | instrUnmodeled a b c => exact .instrUnmodeled a b c
    | syscall _ p => rw [hn] at p; cases p
    | syscallMaterializationFault _ p => rw [hn] at p; cases p
    | exit _ p => rw [hn] at p; cases p
    | killed _ p => rw [hn] at p; cases p
    | syscallUnmodeled _ p => rw [hn] at p; cases p
  · intro h
    cases h with
    | instr a b c => exact .instr a b c
    | instrFault a b c => exact .instrFault a b c
    | instrUnmodeled a b c => exact .instrUnmodeled a b c
    | syscall _ p => rw [hn] at p; cases p
    | syscallMaterializationFault _ p => rw [hn] at p; cases p
    | exit _ p => rw [hn] at p; cases p
    | killed _ p => rw [hn] at p; cases p
    | syscallUnmodeled _ p => rw [hn] at p; cases p

/-- Two tables that agree at a configuration's pending call give it the same steps. -/
theorem sstep_table_congr {isa : UserIsa} {segs : List Segment} {sp₁ sp₂ : Sys SyscallEffect}
    {refused : RefusalFilter} {ms : isa.State} {model : Silmaril.Process.LPS.Model}
    {evs : List Event} {t : StepTo isa}
    (h : ∀ x8, isa.svcPending ms = some x8 → ∀ o,
      sp₁ (sysInput isa segs ms x8) model o ↔ sp₂ (sysInput isa segs ms x8) model o) :
    SStep segs sp₁ refused ⟨ms, model⟩ evs t ↔ SStep segs sp₂ refused ⟨ms, model⟩ evs t := by
  constructor
  · intro st
    cases st with
    | instr a b c => exact .instr a b c
    | instrFault a b c => exact .instrFault a b c
    | instrUnmodeled a b c => exact .instrUnmodeled a b c
    | syscall a p s r l m => exact .syscall a p ((h _ p _).1 s) r l m
    | syscallMaterializationFault a p s r l m =>
      exact .syscallMaterializationFault a p ((h _ p _).1 s) r l m
    | exit a p s hh hk => exact .exit a p ((h _ p _).1 s) hh hk
    | killed a p s k => exact .killed a p ((h _ p _).1 s) k
    | syscallUnmodeled a p s => exact .syscallUnmodeled a p ((h _ p _).1 s)
  · intro st
    cases st with
    | instr a b c => exact .instr a b c
    | instrFault a b c => exact .instrFault a b c
    | instrUnmodeled a b c => exact .instrUnmodeled a b c
    | syscall a p s r l m => exact .syscall a p ((h _ p _).2 s) r l m
    | syscallMaterializationFault a p s r l m =>
      exact .syscallMaterializationFault a p ((h _ p _).2 s) r l m
    | exit a p s hh hk => exact .exit a p ((h _ p _).2 s) hh hk
    | killed a p s k => exact .killed a p ((h _ p _).2 s) k
    | syscallUnmodeled a p s => exact .syscallUnmodeled a p ((h _ p _).2 s)

variable (P : Probe) (oracle : Oracle) {sp : Sys SyscallEffect}

theorem oexec_instrT [Probe.Checked P] {post : Omni.Post (isaOf oracle)} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : Omni.Exec P.segs sp noFilter (P.ocfg oracle core' none counter model) post) :
    Omni.Exec P.segs sp noFilter (P.ocfg oracle core none counter model) post :=
  Omni.exec_of_unique running (fun evs t => (sstep_table_irrel rfl).trans
    (P.osstep_instr_iff oracle running lazy rip fits two notSyscall decoded exec evs t)) rest

theorem oexec_trapT [Probe.Checked P] {post : Omni.Post (isaOf oracle)} {off : Nat}
    {core : Silmaril.X86.State} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : Omni.Exec P.segs sp noFilter (P.ocfg oracle (Probe.complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model) post) :
    Omni.Exec P.segs sp noFilter (P.ocfg oracle core none counter model) post :=
  Omni.exec_of_unique running (fun evs t => (sstep_table_irrel rfl).trans
    (P.osstep_trap_iff oracle running lazy rip two isSyscall evs t)) rest

/-- **A returning call that may change the model**: the outcomes of the table are
`ok (ret x, copyins x) (model' x) (events x)` for the `x` with `allowed x`, each live and with no
lazily mapped pages; the successors are exactly those. -/
theorem osstep_sys_iff {core : Silmaril.X86.State} {n : Word} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} {α : Type} {allowed : α → Prop} {ret : α → Word}
    {copyins : α → List (Word × Nat)} {model' : α → Silmaril.Process.LPS.Model}
    {events : α → List Event} (other : n ≠ 158) (running : model.halted = none)
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, sp (P.sysIn core n) model outcome ↔
      ∃ x, allowed x ∧
        outcome = .ok ((mkEffect (ret x) [] []).withCopyins (copyins x)) (model' x) (events x))
    (evs : List Event) (target : StepTo (isaOf oracle)) :
    SStep P.segs sp noFilter (P.ocfg oracle core (some n) counter model) evs target ↔
      ∃ x, allowed x ∧ evs = events x ∧
        target = .next (P.ocfg oracle (Probe.resume core (ret x)) none counter (model' x)) := by
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s _ _ m =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [Progress.materializeModelAccesses_noLazy _ _ (lazy x hx)] at m
      cases m
      refine ⟨x, hx, rfl, ?_⟩
      rw [P.oresume_effect oracle core n other]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [Progress.materializeModelAccesses_noLazy _ _ (lazy x hx)] at m
      cases m
    | exit _ p s h _ =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [live x hx] at h
      cases h
    | killed _ p s k =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      have := live x hx
      have hk : (model' x).killedBy = none := by
        simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.halted] at this ⊢
        simp [this]
      rw [hk] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨x, hx, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := sp) (refused := noFilter)
      (isa := isaOf oracle) (x8 := n)
      (ms := (⟨⟨⟨core, P.mem0⟩, some n⟩, counter⟩ : X86FlagChoices.State)) running rfl
      ((outcomes _).mpr ⟨x, hx, rfl⟩) (fun h => h) (live x hx)
      (Progress.materializeModelAccesses_noLazy _ _ (lazy x hx))
    rwa [P.oresume_effect oracle core n other] at step

theorem oexec_sys {post : Omni.Post (isaOf oracle)} {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} {α : Type} {allowed : α → Prop}
    {ret : α → Word} {copyins : α → List (Word × Nat)} {model' : α → Silmaril.Process.LPS.Model}
    {events : α → List Event} (other : n ≠ 158) (running : model.halted = none)
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, sp (P.sysIn core n) model outcome ↔
      ∃ x, allowed x ∧
        outcome = .ok ((mkEffect (ret x) [] []).withCopyins (copyins x)) (model' x) (events x))
    (inhabited : ∃ x, allowed x)
    (rest : ∀ x, allowed x → Omni.Exec P.segs sp noFilter
      (P.ocfg oracle (Probe.resume core (ret x)) none counter (model' x))
      (fun trace outcome => post (events x ++ trace) outcome)) :
    Omni.Exec P.segs sp noFilter (P.ocfg oracle core (some n) counter model) post :=
  Omni.exec_of_successors running
    (osstep_sys_iff P oracle other running live lazy outcomes) inhabited rest

/-- **An exit** under any table whose outcomes at the call are the native exit's. -/
theorem oexec_exitT {post : Omni.Post (isaOf oracle)} {core : Silmaril.X86.State}
    {status : Word} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (rdi : core.read .rdi = status) (running : model.halted = none)
    (outcomes : ∀ outcome, sp (P.sysIn core 60) model outcome ↔
      Probes.spec (P.sysIn core 60) model outcome)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core 60) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (P.ocfg oracle core (some 60) counter (model.withHalted (status &&& 255))))) :
    Omni.Exec P.segs sp noFilter (P.ocfg oracle core (some 60) counter model) post := by
  subst rdi
  refine Omni.exec_of_unique (events := [.exitEv (core.read .rdi &&& 255) model.fs])
    (c' := P.ocfg oracle core (some 60) counter (model.withHalted (core.read .rdi &&& 255)))
    running (fun evs t => ?_) (.halt ?_ ?_)
  · refine (sstep_table_congr ?_).trans (P.osstep_exit_iff oracle running clear evs t)
    intro x8 hx o
    cases hx
    exact outcomes o
  · simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted]
  · simpa only [List.append_nil] using done

/-! ## Execution with clone freedom -/

theorem noCloneW_successors {isa : UserIsa} {sg : List Segment} {c : Silmaril.Process.LPS.Config isa}
    (hc : ¬ ClonePending c)
    (rest : ∀ evs c', SStep sg sp noFilter c evs (.next c') → NoCloneFromWith sp sg c') :
    NoCloneFromWith sp sg c := by
  intro tr c'' hs
  cases hs with
  | refl => exact hc
  | step hss hrest => exact rest _ _ hss _ _ hrest

theorem noCloneW_halted {isa : UserIsa} {sg : List Segment} {c : Silmaril.Process.LPS.Config isa}
    (hh : c.model.halted ≠ none) : NoCloneFromWith sp sg c := by
  intro tr c' hs
  cases hs with
  | refl => exact fun h => hh h.1
  | step hss => exact (hh (Omni.sstep_from_running hss)).elim

theorem not_clonePending_none {o : Oracle} {core : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} :
    ¬ ClonePending (P.ocfg o core none counter model) := fun ⟨_, _, hx, _⟩ => by cases hx

theorem not_clonePending_some {o : Oracle} {core : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} {n : Word} (hn : cloneNumber n = false) :
    ¬ ClonePending (P.ocfg o core (some n) counter model) := fun ⟨_, x8, hx, hc⟩ => by
  cases hx
  rw [hn] at hc
  cases hc

theorem oexecN_instr [Probe.Checked P] {post : Omni.Post (isaOf oracle)} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : ExecN P.segs sp (P.ocfg oracle core' none counter model) post) :
    ExecN P.segs sp (P.ocfg oracle core none counter model) post := by
  have succ := fun evs t => (sstep_table_irrel (sp₁ := sp) (sp₂ := Probes.spec) (segs := P.segs)
    (refused := noFilter) (c := P.ocfg oracle core none counter model) (evs := evs) (t := t) rfl).trans
    (P.osstep_instr_iff oracle running lazy rip fits two notSyscall decoded exec evs t)
  refine ⟨Omni.exec_of_unique running succ rest.1, noCloneW_successors (not_clonePending_none P) ?_⟩
  intro evs c' hs
  obtain ⟨-, ht⟩ := (succ _ _).1 hs
  cases ht
  exact rest.2

theorem oexecN_trap [Probe.Checked P] {post : Omni.Post (isaOf oracle)} {off : Nat}
    {core : Silmaril.X86.State} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : ExecN P.segs sp (P.ocfg oracle (Probe.complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model) post) :
    ExecN P.segs sp (P.ocfg oracle core none counter model) post := by
  have succ := fun evs t => (sstep_table_irrel (sp₁ := sp) (sp₂ := Probes.spec) (segs := P.segs)
    (refused := noFilter) (c := P.ocfg oracle core none counter model) (evs := evs) (t := t) rfl).trans
    (P.osstep_trap_iff oracle running lazy rip two isSyscall evs t)
  refine ⟨Omni.exec_of_unique running succ rest.1, noCloneW_successors (not_clonePending_none P) ?_⟩
  intro evs c' hs
  obtain ⟨-, ht⟩ := (succ _ _).1 hs
  cases ht
  exact rest.2

theorem oexecN_sys {post : Omni.Post (isaOf oracle)} {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} {α : Type} {allowed : α → Prop}
    {ret : α → Word} {copyins : α → List (Word × Nat)} {model' : α → Silmaril.Process.LPS.Model}
    {events : α → List Event} (other : n ≠ 158) (notClone : cloneNumber n = false)
    (running : model.halted = none)
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, sp (P.sysIn core n) model outcome ↔
      ∃ x, allowed x ∧
        outcome = .ok ((mkEffect (ret x) [] []).withCopyins (copyins x)) (model' x) (events x))
    (inhabited : ∃ x, allowed x)
    (rest : ∀ x, allowed x → ExecN P.segs sp
      (P.ocfg oracle (Probe.resume core (ret x)) none counter (model' x))
      (fun trace outcome => post (events x ++ trace) outcome)) :
    ExecN P.segs sp (P.ocfg oracle core (some n) counter model) post := by
  have succ := osstep_sys_iff P oracle (counter := counter) other running live lazy outcomes
  refine ⟨Omni.exec_of_successors running succ inhabited fun x hx => (rest x hx).1,
    noCloneW_successors (not_clonePending_some P notClone) ?_⟩
  intro evs c' hs
  obtain ⟨x, hx, -, ht⟩ := (succ _ _).1 hs
  cases ht
  exact (rest x hx).2

theorem oexecN_exit {post : Omni.Post (isaOf oracle)} {core : Silmaril.X86.State}
    {status : Word} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (rdi : core.read .rdi = status) (running : model.halted = none)
    (outcomes : ∀ outcome, sp (P.sysIn core 60) model outcome ↔
      Probes.spec (P.sysIn core 60) model outcome)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core 60) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (P.ocfg oracle core (some 60) counter (model.withHalted (status &&& 255))))) :
    ExecN P.segs sp (P.ocfg oracle core (some 60) counter model) post := by
  refine ⟨oexec_exitT P oracle rdi running outcomes clear done, ?_⟩
  subst rdi
  have succ : ∀ evs t, SStep P.segs sp noFilter (P.ocfg oracle core (some 60) counter model) evs t ↔
      evs = [.exitEv (core.read .rdi &&& 255) model.fs] ∧
        t = .next (P.ocfg oracle core (some 60) counter (model.withHalted (core.read .rdi &&& 255))) := by
    intro evs t
    refine (sstep_table_congr ?_).trans (P.osstep_exit_iff oracle running clear evs t)
    intro x8 hx o
    cases hx
    exact outcomes o
  refine noCloneW_successors (not_clonePending_some P (by decide)) ?_
  intro evs c' hs
  obtain ⟨-, ht⟩ := (succ _ _).1 hs
  cases ht
  exact noCloneW_halted (by simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted])

/-! ## Rules over a changed memory -/

theorem oaccountStep_instrW [Probe.Checked P] {mem : Silmaril.Process.Memory} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (fetched : mem.fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len))
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core mem len = .ok core' mem) :
    accountStep (isaOf oracle) P.segs ⟨⟨⟨core, mem⟩, none⟩, counter⟩ model =
      .ok (⟨⟨⟨core', mem⟩, none⟩, counter⟩, model) := by
  have notTwo : mem.fetchBytes core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    rw [rip, prefix2]
    exact fun h => notSyscall (Option.some.inj h)
  apply Progress.accountStep_of_noLazy _ _ model _ lazy
  change X86FlagChoices.step oracle ⟨⟨⟨core, mem⟩, none⟩, counter⟩ = _
  rw [X86FlagChoices.step_not_syscall _ _ notTwo]
  rw [x86NativeStep_of_fetch (s := ⟨⟨core, mem⟩, none⟩) notTwo
    (show mem.fetchBytes core.rip.toNat len = some _ by rw [rip, fetched]) decoded]
  change X86FlagChoices.lift counter
    (x86ExecResult _ (Silmaril.X86.Ext.exec instruction core mem len)) = _
  rw [exec]
  rfl

theorem oexecN_instrW [Probe.Checked P] {post : Omni.Post (isaOf oracle)} {mem : Silmaril.Process.Memory}
    {off len : Nat} {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} (running : model.halted = none)
    (lazy : model.vmLazy = []) (rip : core.rip.toNat = P.base + off)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (fetched : mem.fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len))
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core mem len = .ok core' mem)
    (rest : ExecN P.segs sp (ocfgM oracle core' mem none counter model) post) :
    ExecN P.segs sp (ocfgM oracle core mem none counter model) post := by
  have account := oaccountStep_instrW P oracle (counter := counter) lazy rip notSyscall fetched prefix2
    decoded exec
  have succ : ∀ evs t, SStep P.segs sp noFilter (ocfgM oracle core mem none counter model) evs t ↔
      evs = [] ∧ t = .next (ocfgM oracle core' mem none counter model) := by
    intro evs t
    constructor
    · intro step
      cases step with
      | instr _ _ h => rw [account] at h; cases h; exact ⟨rfl, rfl⟩
      | instrFault _ _ h => rw [account] at h; cases h
      | instrUnmodeled _ _ h => rw [account] at h; cases h
      | syscall _ p => cases p
      | syscallMaterializationFault _ p => cases p
      | exit _ p => cases p
      | killed _ p => cases p
      | syscallUnmodeled _ p => cases p
    · rintro ⟨rfl, rfl⟩
      exact .instr running rfl account
  refine ⟨Omni.exec_of_unique running succ rest.1,
    noCloneW_successors (fun ⟨_, _, hx, _⟩ => by cases hx) ?_⟩
  intro evs c' hs
  obtain ⟨-, ht⟩ := (succ _ _).1 hs
  cases ht
  exact rest.2

theorem oexecN_trapW [Probe.Checked P] {post : Omni.Post (isaOf oracle)} {mem : Silmaril.Process.Memory}
    {off : Nat} {core : Silmaril.X86.State} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : ExecN P.segs sp (ocfgM oracle (Probe.complete core (oracle counter)) mem
      (some (core.read .rax)) (counter + 1) model) post) :
    ExecN P.segs sp (ocfgM oracle core mem none counter model) post := by
  have account : accountStep (isaOf oracle) P.segs ⟨⟨⟨core, mem⟩, none⟩, counter⟩
      model = .ok (⟨⟨⟨Probe.complete core (oracle counter), mem⟩, some (core.read .rax)⟩,
        counter + 1⟩, model) := by
    apply Progress.accountStep_of_noLazy _ _ model _ lazy
    exact X86FlagChoices.step_syscall oracle ⟨⟨⟨core, mem⟩, none⟩, counter⟩
      (by rw [show core.rip.toNat = P.base + off from rip, prefix2, isSyscall])
  have succ : ∀ evs t, SStep P.segs sp noFilter (ocfgM oracle core mem none counter model) evs t ↔
      evs = [] ∧ t = .next (ocfgM oracle (Probe.complete core (oracle counter)) mem
        (some (core.read .rax)) (counter + 1) model) := by
    intro evs t
    constructor
    · intro step
      cases step with
      | instr _ _ h => rw [account] at h; cases h; exact ⟨rfl, rfl⟩
      | instrFault _ _ h => rw [account] at h; cases h
      | instrUnmodeled _ _ h => rw [account] at h; cases h
      | syscall _ p => cases p
      | syscallMaterializationFault _ p => cases p
      | exit _ p => cases p
      | killed _ p => cases p
      | syscallUnmodeled _ p => cases p
    · rintro ⟨rfl, rfl⟩
      exact .instr running rfl account
  refine ⟨Omni.exec_of_unique running succ rest.1,
    noCloneW_successors (fun ⟨_, _, hx, _⟩ => by cases hx) ?_⟩
  intro evs c' hs
  obtain ⟨-, ht⟩ := (succ _ _).1 hs
  cases ht
  exact rest.2

/-- **A call whose only outcome halts**, over any memory. -/
theorem oexecN_haltW {post : Omni.Post (isaOf oracle)} {mem : Silmaril.Process.Memory}
    {core : Silmaril.X86.State} {n : Word} {counter : Nat} {model model' : Silmaril.Process.LPS.Model}
    {effect : SyscallEffect} {code : Word} (notClone : cloneNumber n = false)
    (running : model.halted = none)
    (outcomes : ∀ outcome, sp (sysInput (isaOf oracle) P.segs
        (⟨⟨⟨core, mem⟩, some n⟩, counter⟩ : X86FlagChoices.State) n) model outcome ↔
      outcome = .ok effect model' [])
    (halted : model'.halted = some code) (unkilled : model'.killedBy = none)
    (done : post [.exitEv code model'.fs] (.halt (ocfgM oracle core mem (some n) counter model'))) :
    ExecN P.segs sp (ocfgM oracle core mem (some n) counter model) post := by
  have succ : ∀ evs t, SStep P.segs sp noFilter (ocfgM oracle core mem (some n) counter model) evs t ↔
      evs = [.exitEv code model'.fs] ∧ t = .next (ocfgM oracle core mem (some n) counter model') := by
    intro evs t
    constructor
    · intro step
      cases step with
      | instr _ p => cases p
      | instrFault _ p => cases p
      | instrUnmodeled _ p => cases p
      | syscall _ p s _ live =>
        cases p
        cases (outcomes _).mp s
        rw [halted] at live
        cases live
      | syscallMaterializationFault _ p s _ live =>
        cases p
        cases (outcomes _).mp s
        rw [halted] at live
        cases live
      | exit _ p s h _ =>
        cases p
        cases (outcomes _).mp s
        rw [halted] at h
        cases h
        exact ⟨rfl, rfl⟩
      | killed _ p s k =>
        cases p
        cases (outcomes _).mp s
        rw [unkilled] at k
        cases k
      | syscallUnmodeled _ p s =>
        cases p
        cases (outcomes _).mp s
    · rintro ⟨rfl, rfl⟩
      exact SStep.exit (isa := isaOf oracle)
        (ms := (⟨⟨⟨core, mem⟩, some n⟩, counter⟩ : X86FlagChoices.State))
        running rfl ((outcomes _).mpr rfl) halted unkilled
  have hh : model'.halted ≠ none := by rw [halted]; simp
  refine ⟨Omni.exec_of_unique running succ (.halt hh (by simpa using done)), ?_⟩
  refine noCloneW_successors (fun ⟨_, x8, hx, hc⟩ => by cases hx; rw [notClone] at hc; cases hc) ?_
  intro evs c' hs
  obtain ⟨-, ht⟩ := (succ _ _).1 hs
  cases ht
  exact noCloneW_halted hh

theorem oresume_effectW (core : Silmaril.X86.State) (mem mem' : Silmaril.Process.Memory) (n : Word)
    (other : n ≠ 158) (ret : Word) (writes : List (Word × List Byte)) (copyins : List (Word × Nat))
    (counter : Nat)
    (applied : applyMemoryEffect mem ((mkEffect ret writes []).withCopyins copyins) = mem') :
    (isaOf oracle).advancePastSvc ((isaOf oracle).applyEffect
      (⟨⟨⟨core, mem⟩, some n⟩, counter⟩ : X86FlagChoices.State)
      ((mkEffect ret writes []).withCopyins copyins)) = ⟨⟨⟨Probe.resume core ret, mem'⟩, none⟩, counter⟩ := by
  change (⟨x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, mem⟩, some n⟩
    ((mkEffect ret writes []).withCopyins copyins)), counter⟩ : X86FlagChoices.State) = _
  rw [Probe.resume_effectW core mem mem' n other ret writes copyins applied]

/-- **A returning call that may write memory and change the model.** -/
theorem oexecN_sysW {post : Omni.Post (isaOf oracle)} {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} {α : Type} {allowed : α → Prop}
    {ret : α → Word} {writes : α → List (Word × List Byte)} {copyins : α → List (Word × Nat)}
    {model' : α → Silmaril.Process.LPS.Model} {events : α → List Event}
    {mem' : α → Silmaril.Process.Memory} (other : n ≠ 158) (notClone : cloneNumber n = false)
    (running : model.halted = none)
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, sp (P.sysIn core n) model outcome ↔
      ∃ x, allowed x ∧ outcome =
        .ok ((mkEffect (ret x) (writes x) []).withCopyins (copyins x)) (model' x) (events x))
    (applied : ∀ x, allowed x →
      applyMemoryEffect P.mem0 ((mkEffect (ret x) (writes x) []).withCopyins (copyins x)) = mem' x)
    (inhabited : ∃ x, allowed x)
    (rest : ∀ x, allowed x → ExecN P.segs sp
      (ocfgM oracle (Probe.resume core (ret x)) (mem' x) none counter (model' x))
      (fun trace outcome => post (events x ++ trace) outcome)) :
    ExecN P.segs sp (P.ocfg oracle core (some n) counter model) post := by
  have succ : ∀ evs t, SStep P.segs sp noFilter (P.ocfg oracle core (some n) counter model) evs t ↔
      ∃ x, allowed x ∧ evs = events x ∧
        t = .next (ocfgM oracle (Probe.resume core (ret x)) (mem' x) none counter (model' x)) := by
    intro evs t
    constructor
    · intro step
      cases step with
      | instr _ p => cases p
      | instrFault _ p => cases p
      | instrUnmodeled _ p => cases p
      | syscall _ p s _ _ m =>
        cases p
        obtain ⟨x, hx, same⟩ := (outcomes _).mp s
        cases same
        rw [Progress.materializeModelAccesses_noLazy _ _ (lazy x hx)] at m
        cases m
        refine ⟨x, hx, rfl, ?_⟩
        rw [oresume_effectW oracle core P.mem0 (mem' x) n other _ _ _ counter (applied x hx)]
      | syscallMaterializationFault _ p s _ _ m =>
        cases p
        obtain ⟨x, hx, same⟩ := (outcomes _).mp s
        cases same
        rw [Progress.materializeModelAccesses_noLazy _ _ (lazy x hx)] at m
        cases m
      | exit _ p s h _ =>
        cases p
        obtain ⟨x, hx, same⟩ := (outcomes _).mp s
        cases same
        rw [live x hx] at h
        cases h
      | killed _ p s k =>
        cases p
        obtain ⟨x, hx, same⟩ := (outcomes _).mp s
        cases same
        have := live x hx
        have hk : (model' x).killedBy = none := by
          simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.halted] at this ⊢
          simp [this]
        rw [hk] at k
        cases k
      | syscallUnmodeled _ p s =>
        cases p
        obtain ⟨x, _, same⟩ := (outcomes _).mp s
        cases same
    · rintro ⟨x, hx, rfl, rfl⟩
      have step := SStep.syscall (segs := P.segs) (spec := sp) (refused := noFilter)
        (isa := isaOf oracle) (x8 := n)
        (ms := (⟨⟨⟨core, P.mem0⟩, some n⟩, counter⟩ : X86FlagChoices.State)) running rfl
        ((outcomes _).mpr ⟨x, hx, rfl⟩) (fun h => h) (live x hx)
        (Progress.materializeModelAccesses_noLazy _ _ (lazy x hx))
      rwa [oresume_effectW oracle core P.mem0 (mem' x) n other _ _ _ counter (applied x hx)] at step
  refine ⟨Omni.exec_of_successors running succ inhabited fun x hx => (rest x hx).1,
    noCloneW_successors (not_clonePending_some P notClone) ?_⟩
  intro evs c' hs
  obtain ⟨x, hx, -, ht⟩ := (succ _ _).1 hs
  cases ht
  exact (rest x hx).2

end Silmaril.Proofs.Containers.Lps.Kit
