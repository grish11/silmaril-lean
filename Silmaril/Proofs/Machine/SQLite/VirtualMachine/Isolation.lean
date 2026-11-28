module

public import Silmaril.Machine.SQLite.VirtualMachine.Isolation.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Isolation

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Isolation

theorem effect_isBad_iff (profile : Profile) (e : Effect) :
    e.isBad profile = true ↔ e.Bad profile := by
  cases e <;> simp [Effect.isBad, Effect.Bad]

theorem withinProfile_iff (profile : Profile) (instr : Instruction) :
    withinProfile profile instr = true ↔ InstructionInProfile profile instr := by
  cases instr <;> simp [withinProfile, InstructionInProfile]

theorem stateInv_initial (profile : Profile) (host : HostState) :
    StateInv profile host initial where
  registersConfined := fun _ h => False.elim (h rfl)
  cursorsConfined := fun _ _ h => by cases h
  rowsBounded := fun _ h => by cases h

private theorem stateInv_advance {profile : Profile} {host : HostState} {s : State}
    (hinv : StateInv profile host s) :
    StateInv profile host s.advance :=
  ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩

private theorem stateInv_jump {profile : Profile} {host : HostState} {s : State} {target : Nat}
    (hinv : StateInv profile host s) :
    StateInv profile host (s.jump target) :=
  ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩

private theorem stateInv_write {profile : Profile} {host : HostState} {s : State}
    {dest : Nat} {val : Value}
    (hinv : StateInv profile host s)
    (hdest : 1 ≤ dest ∧ dest ≤ profile.maxRegisters) :
    StateInv profile host (s.write dest val) where
  registersConfined := by
    intro r hr
    by_cases heq : r = dest
    · subst heq; exact hdest
    · apply hinv.registersConfined r
      simpa [Vdbe.State.write, heq] using hr
  cursorsConfined := hinv.cursorsConfined
  rowsBounded := hinv.rowsBounded

private theorem stateInv_writeNull {profile : Profile} {host : HostState} {s : State}
    {first last : Nat} (hinv : StateInv profile host s) :
    StateInv profile host (s.writeNull first last) where
  registersConfined := by
    intro r hr
    by_cases hin : first ≤ r ∧ r ≤ max first last
    · exfalso
      simp only [Vdbe.State.writeNull, ite_eq_left hin] at hr
      exact hr rfl
    · apply hinv.registersConfined r
      simpa only [Vdbe.State.writeNull, ite_eq_right hin] using hr
  cursorsConfined := hinv.cursorsConfined
  rowsBounded := hinv.rowsBounded

private theorem stateInv_copyRegisters {profile : Profile} {host : HostState} :
    ∀ (count src dst : Nat) (s : State),
      StateInv profile host s →
      (count = 0 ∨ (1 ≤ dst ∧ dst + count - 1 ≤ profile.maxRegisters)) →
      StateInv profile host (Vdbe.State.copyRegisters count src dst s)
  | 0, _, _, s, hinv, _ => hinv
  | count + 1, src, dst, s, hinv, hbounds => by
      have hdst : 1 ≤ dst ∧ dst ≤ profile.maxRegisters := by
        rcases hbounds with h0 | ⟨h1, h2⟩
        · cases h0
        · exact ⟨h1, by omega⟩
      have hnext : count = 0 ∨ (1 ≤ dst + 1 ∧ (dst + 1) + count - 1 ≤ profile.maxRegisters) := by
        cases count with
        | zero => exact Or.inl rfl
        | succ k =>
            rcases hbounds with h0 | ⟨h1, h2⟩
            · cases h0
            · exact Or.inr ⟨by omega, by omega⟩
      exact stateInv_copyRegisters count (src + 1) (dst + 1)
        (s.write dst (s.registers src))
        (stateInv_write hinv hdst)
        hnext

private theorem stateInv_setCursor_authorized {profile : Profile} {host : HostState} {s : State}
    {cid db root : Nat} {cursor : Vdbe.Cursor}
    (hinv : StateInv profile host s)
    (hcid : cid < profile.maxCursors)
    (hauth : profile.canRead db root = true)
    (hfound : host.databases db root = some cursor.table) :
    StateInv profile host (s.setCursor cid cursor) where
  registersConfined := hinv.registersConfined
  cursorsConfined := by
    intro id c hc
    by_cases heq : id = cid
    · subst heq
      simp only [Vdbe.State.setCursor, ↓reduceIte, Option.some.injEq] at hc
      subst hc
      exact ⟨hcid, db, root, hauth, hfound⟩
    · apply hinv.cursorsConfined id c
      simpa [Vdbe.State.setCursor, heq] using hc
  rowsBounded := hinv.rowsBounded

private theorem stateInv_updateCursor {profile : Profile} {host : HostState} {s : State}
    {cid : Nat} {cursor cursor' : Vdbe.Cursor}
    (hinv : StateInv profile host s)
    (hcur : s.cursors cid = some cursor)
    (htab : cursor'.table = cursor.table) :
    StateInv profile host (s.setCursor cid cursor') := by
  obtain ⟨hcid, db, root, hauth, hfound⟩ := hinv.cursorsConfined cid cursor hcur
  exact stateInv_setCursor_authorized hinv hcid hauth (htab ▸ hfound)

private theorem stateInv_emit {profile : Profile} {host : HostState} {s : State}
    {first count : Nat}
    (hinv : StateInv profile host s)
    (hwidth : count ≤ profile.maxResultWidth) :
    StateInv profile host (s.emit first count) where
  registersConfined := hinv.registersConfined
  cursorsConfined := hinv.cursorsConfined
  rowsBounded := by
    intro row hrow
    simp only [Vdbe.State.emit, List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hold | rfl
    · exact hinv.rowsBounded row hold
    · simpa [List.length_map, List.length_range] using hwidth

theorem execute_preserves_stateInv {profile : Profile} {host : HostState}
    {instr : Instruction} {s s' : State}
    (hprof : InstructionInProfile profile instr)
    (hinv : StateInv profile host s)
    (hexec : Vdbe.execute host.databases instr s = .ok s') :
    StateInv profile host s' := by
  cases instr with
  | init target =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_jump hinv
  | goto target =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_jump hinv
  | halt code =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩
  | integer value destination =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_write hinv hprof)
  | int64 value destination =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_write hinv hprof)
  | string8 value destination =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_write hinv hprof)
  | null first last =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_writeNull hinv)
  | copy source destination additional =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      have hdest1 : 1 ≤ destination := hprof.1
      have hdest2 : destination + additional ≤ profile.maxRegisters := hprof.2
      have hbounds :
          additional + 1 = 0 ∨ (1 ≤ destination ∧ destination + (additional + 1) - 1 ≤ profile.maxRegisters) :=
        Or.inr ⟨hdest1, by omega⟩
      exact stateInv_advance (stateInv_copyRegisters (additional + 1) source destination s hinv hbounds)
  | openRead cursor root database =>
      simp only [Vdbe.execute] at hexec
      cases hdb : host.databases database root with
      | none =>
          simp [hdb] at hexec
      | some table =>
          simp only [hdb, Except.ok.injEq] at hexec
          subst hexec
          exact stateInv_advance (stateInv_setCursor_authorized hinv hprof.2 hprof.1 hdb)
  | rewind cursor target =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          split at hexec
          · cases hexec
          · simp only [Except.ok.injEq] at hexec
            subst hexec
            exact stateInv_jump (stateInv_updateCursor hinv hcur rfl)
  | next cursor target =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          split at hexec
          · cases hexec
          · cases hrem : c.remaining with
            | none =>
                simp [hrem] at hexec
            | some rem =>
                simp only [hrem, Except.ok.injEq] at hexec
                subst hexec
                exact stateInv_jump (stateInv_updateCursor hinv hcur rfl)
  | column cursor col destination =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          cases hrow : c.current? with
          | none =>
              simp [hrow] at hexec
          | some entry =>
              simp only [hrow, Except.ok.injEq] at hexec
              subst hexec
              exact stateInv_advance (stateInv_write hinv hprof.2)
  | rowid cursor destination =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          cases hrow : c.current? with
          | none =>
              simp [hrow] at hexec
          | some entry =>
              simp only [hrow] at hexec
              split at hexec
              · simp only [Except.ok.injEq] at hexec
                subst hexec
                exact stateInv_advance (stateInv_write hinv hprof.2)
              · cases hexec
  | resultRow first count =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_emit hinv hprof)
  | seekRowid cursor target keyRegister =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          cases hreg : s.registers keyRegister with
          | integer key =>
              simp only [hreg] at hexec
              split at hexec
              · cases hexec
              · simp only [Except.ok.injEq] at hexec
                subst hexec
                exact stateInv_jump (stateInv_updateCursor hinv hcur rfl)
          | null | real _ | text _ | blob _ =>
              simp [hreg] at hexec

theorem modeledEffects_not_bad {profile : Profile} {instr : Instruction}
    (hprof : InstructionInProfile profile instr) (s : State) (outcome : Except Fault State) :
    ∀ e ∈ modeledEffects instr s outcome, ¬ e.Bad profile := by
  intro e he
  cases instr with
  | openRead cursor root database =>
      cases outcome with
      | ok _ =>
          simp only [modeledEffects, List.mem_singleton] at he
          subst he
          simp [Effect.Bad, hprof.1]
      | error _ =>
          simp only [modeledEffects, List.mem_singleton] at he
          subst he
          simp [Effect.Bad, hprof.1]
  | resultRow first count =>
      cases outcome with
      | ok _ =>
          simp only [modeledEffects, List.mem_singleton] at he
          subst he
          simp only [Effect.Bad, List.length_map, List.length_range]
          exact Nat.not_lt.mpr hprof
      | error _ =>
          simp [modeledEffects] at he
  | init _ | goto _ | halt _ | integer _ _ | int64 _ _ | string8 _ _
  | null _ _ | copy _ _ _ | rewind _ _ | next _ _ | column _ _ _
  | rowid _ _ | seekRowid _ _ _ =>
      simp [modeledEffects] at he

theorem profileStep_safe {profile : Profile} {fallback : Fallback}
    (hsafe : FallbackSafe profile fallback) {raw : Vdbe.RawProgram}
    {host host' : HostState} {s s' : State} {evs : List Effect}
    (hinv : StateInv profile host s)
    (hstep : ProfileStep profile fallback raw (host, s) evs (host', s')) :
    (∀ e ∈ evs, ¬ e.Bad profile) ∧ host' = host ∧ StateInv profile host' s' := by
  cases hstep with
  | modeledOk _ _ _ inProfile exec =>
      have hprof := (withinProfile_iff profile _).mp inProfile
      exact ⟨modeledEffects_not_bad hprof s (.ok s'), rfl,
        execute_preserves_stateInv hprof hinv exec⟩
  | modeledFault _ _ _ inProfile _ code =>
      have hprof := (withinProfile_iff profile _).mp inProfile
      exact ⟨modeledEffects_not_bad hprof s (.error _), rfl,
        ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩⟩
  | fallbackStep _ _ _ hfb =>
      exact hsafe _ host s evs host' s' hinv hfb

theorem profileTrace_safe_from {profile : Profile} {fallback : Fallback}
    (hsafe : FallbackSafe profile fallback) {raw : Vdbe.RawProgram}
    {cfg1 cfg2 : HostState × State} {evs : List Effect}
    (hinv : StateInv profile cfg1.1 cfg1.2)
    (htrace : ProfileTrace profile fallback raw cfg1 evs cfg2) :
    (∀ e ∈ evs, ¬ e.Bad profile) ∧ cfg2.1 = cfg1.1 ∧ StateInv profile cfg2.1 cfg2.2 := by
  induction htrace with
  | nil cfg =>
      exact ⟨(fun _ h => by cases h), rfl, hinv⟩
  | @cons cfg1 cfg2 cfg3 evs1 evs2 hstep _ ih =>
      rcases cfg1 with ⟨h1, s1⟩
      rcases cfg2 with ⟨h2, s2⟩
      obtain ⟨hev1, hh12, hinv2⟩ := profileStep_safe hsafe hinv hstep
      obtain ⟨hev2, hh23, hinv3⟩ := ih hinv2
      refine ⟨?_, hh23.trans hh12, hinv3⟩
      intro e he
      rcases List.mem_append.mp he with he1 | he2
      · exact hev1 e he1
      · exact hev2 e he2

theorem profileTrace_safe {profile : Profile} {fallback : Fallback}
    (hsafe : FallbackSafe profile fallback)
    (host : HostState) (raw : Vdbe.RawProgram)
    {evs : List Effect} {host' : HostState} {s' : State}
    (htrace : ProfileTrace profile fallback raw (host, initial) evs (host', s')) :
    (∀ e ∈ evs, ¬ e.Bad profile) ∧ host' = host ∧ StateInv profile host' s' :=
  profileTrace_safe_from hsafe (stateInv_initial profile host) htrace

theorem stepProfile_safe {profile : Profile} {host : HostState}
    (raw : Vdbe.RawProgram) {s : State} (hinv : StateInv profile host s) :
    (∀ e ∈ (stepProfile profile host raw s).1, ¬ e.Bad profile) ∧
    (∀ host' s', (stepProfile profile host raw s).2 = .ok (host', s') →
      host' = host ∧ StateInv profile host' s') := by
  unfold stepProfile
  by_cases hhalt : s.halted.isSome
  · simp [hhalt]
  · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
    cases hpc : raw[s.pc]? with
    | none =>
        simp
    | some rawInstr =>
        simp only
        cases hdec : Vdbe.decode? rawInstr with
        | none =>
            simp
        | some instr =>
            simp only
            cases hwp : withinProfile profile instr with
            | false =>
                simp
            | true =>
                have hprof := (withinProfile_iff profile instr).mp hwp
                simp only [↓reduceIte]
                refine ⟨modeledEffects_not_bad hprof s _, ?_⟩
                intro host' s' hok
                cases hexec : Vdbe.execute host.databases instr s with
                | error err =>
                    simp [hexec] at hok
                | ok after =>
                    simp only [hexec, Except.ok.injEq, Prod.mk.injEq] at hok
                    rcases hok with ⟨rfl, rfl⟩
                    exact ⟨rfl, execute_preserves_stateInv hprof hinv hexec⟩

theorem runProfile_safe_from (profile : Profile) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) {s : State}
    (hinv : StateInv profile host s) :
    (∀ e ∈ (runProfile profile host raw fuel s).events, ¬ e.Bad profile) ∧
    (runProfile profile host raw fuel s).host = host ∧
    StateInv profile (runProfile profile host raw fuel s).host
      (runProfile profile host raw fuel s).result.state := by
  induction fuel generalizing s with
  | zero =>
      by_cases hhalt : s.halted.isSome <;>
        simp [runProfile, ProfileRunResult.state, hhalt, hinv]
  | succ fuel ih =>
      by_cases hhalt : s.halted.isSome
      · simp [runProfile, ProfileRunResult.state, hhalt, hinv]
      · obtain ⟨heff, hok⟩ := stepProfile_safe raw hinv
        cases hstep : (stepProfile profile host raw s).2 with
        | error fault =>
            simp only [runProfile, hhalt, Bool.false_eq_true, ↓reduceIte, hstep,
              ProfileRunResult.state]
            exact ⟨heff, trivial, hinv⟩
        | ok pair =>
            rcases pair with ⟨host', after⟩
            obtain ⟨rfl, hinv'⟩ := hok host' after hstep
            obtain ⟨hevRest, hhostRest, hinvRest⟩ := ih hinv'
            simp only [runProfile, hhalt, Bool.false_eq_true, ↓reduceIte, hstep]
            refine ⟨?_, hhostRest, hinvRest⟩
            intro e he
            rcases List.mem_append.mp he with h1 | h2
            · exact heff e h1
            · exact hevRest e h2

theorem runProfile_safe (profile : Profile) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) :
    (∀ e ∈ (runProfile profile host raw fuel initial).events, ¬ e.Bad profile) ∧
    (runProfile profile host raw fuel initial).host = host ∧
    StateInv profile (runProfile profile host raw fuel initial).host
      (runProfile profile host raw fuel initial).result.state :=
  runProfile_safe_from profile host raw fuel (stateInv_initial profile host)

theorem runProfile_no_bad_effects (profile : Profile) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) :
    ∀ e ∈ (runProfile profile host raw fuel initial).events,
      (∀ db root, e ≠ .writeTable db root) ∧
      (∀ name, e ≠ .attachDb name) ∧
      (∀ path, e ≠ .loadExtension path) ∧
      (∀ op, e ≠ .hostEscape op) ∧
      (∀ db root found, e = .readTable db root found → profile.canRead db root = true) ∧
      (∀ cells, e = .emitRow cells → cells.length ≤ profile.maxResultWidth) := by
  have hsafe := (runProfile_safe profile host raw fuel).1
  intro e he
  have hnb := hsafe e he
  cases e with
  | readTable db root found =>
      refine ⟨(by intro _ _ h; cases h), (by intro _ h; cases h), (by intro _ h; cases h),
        (by intro _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro db' root' found' h
      cases h
      cases hdb : profile.canRead db root
      · exact False.elim (hnb hdb)
      · rfl
  | emitRow cells =>
      refine ⟨(by intro _ _ h; cases h), (by intro _ h; cases h), (by intro _ h; cases h),
        (by intro _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
      intro cells' h
      cases h
      exact Nat.le_of_not_lt hnb
  | writeTable _ _ => exact False.elim (hnb trivial)
  | attachDb _ => exact False.elim (hnb trivial)
  | loadExtension _ => exact False.elim (hnb trivial)
  | hostEscape _ => exact False.elim (hnb trivial)

theorem stepProfile_eq_vm_execute {profile : Profile} {host : HostState}
    {raw : Vdbe.RawProgram} {s : State} {rawInstr : RawInstruction} {instr : Instruction}
    (hactive : s.halted = none)
    (hfetch : raw[s.pc]? = some rawInstr)
    (hdec : Vdbe.decode? rawInstr = some instr)
    (hwp : withinProfile profile instr = true) :
    (stepProfile profile host raw s).2 =
      match Vdbe.execute host.databases instr s with
      | .ok s' => .ok (host, s')
      | .error err => .error (.vm err) := by
  simp only [stepProfile, hactive, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    hfetch, hdec, hwp]
  rfl

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Isolation
