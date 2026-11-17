module

public import Silmaril.Containers.Lps.Defs

/-!
# Proofs: the runs of the LPS adapter for programs that only exit

Proofs for `Silmaril.Containers.Lps.Thms`. Nothing imports this module except that header.

The argument: from a configuration `c` of a fixed oracle, the invariant `Inv k c` says that every
maximal LPS execution from `c` is finite, error free, has only stop events and halts with status
`k` (`Omni.Exec … (Post k)`), and that no configuration reachable from `c` is about to create a
task. Under it every adapter step is an internal LPS step to a configuration satisfying it again
(`step_inv`), so adapter executions emit nothing (`exec_inv`), adapter paths are finite
(`not_silentDiv`), no state is stuck (`not_stuck`), and the only stop is `exited k`
(`final_inv`).
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Lps

open Silmaril.Containers Silmaril.Containers.Mach Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines

/-! ## Stop events -/

theorem mapM_stopOnly : ∀ {tr : List Event}, StopOnly tr → tr.mapM mapEv = some (tr.map fun _ => [])
  | [], _ => rfl
  | e :: tr, h => by
    have he := h e (.head _)
    have ih := mapM_stopOnly (tr := tr) fun x hx => h x (.tail _ hx)
    simp only [List.mapM_cons, ih, List.map_cons]
    cases e <;> first | exact he.elim | rfl

theorem mapEvs_stopOnly {tr : List Event} (h : StopOnly tr) : mapEvs tr = some [] := by
  unfold mapEvs
  rw [mapM_stopOnly h]
  simp

theorem stopOnly_append {a b : List Event} : StopOnly (a ++ b) ↔ StopOnly a ∧ StopOnly b :=
  ⟨fun h => ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩,
    fun ⟨ha, hb⟩ e he => (List.mem_append.1 he).elim (ha e) (hb e)⟩

/-! ## The postcondition and the invariant -/

variable {o : Oracle} {segs : List Segment} {k : Word}

/-- **The invariant.** -/
def Inv (segs : List Segment) (k : Word) (c : Silmaril.Process.LPS.Config (isaOf o)) : Prop :=
  Omni.Exec segs Probes.spec noFilter c (Post k) ∧ NoCloneFrom segs c

/-- The adapter state of a configuration with nothing pending and no undefined behaviour. -/
def stOf (o : Oracle) (segs : List Segment) (c : Silmaril.Process.LPS.Config (isaOf o)) : St :=
  ⟨o, segs, c, [], none⟩

theorem stOf_inj {c₁ c₂ : Silmaril.Process.LPS.Config (isaOf o)}
    (h : stOf o segs c₁ = stOf o segs c₂) : c₁ = c₂ := by
  unfold stOf at h
  cases h
  rfl

/-- After an LPS step from a configuration satisfying the invariant, the step's events are stop
events and the invariant holds again. -/
theorem inv_next {c c' : Silmaril.Process.LPS.Config (isaOf o)} {evs : List Event}
    (hi : Inv segs k c) (hs : SStep segs Probes.spec noFilter c evs (.next c')) :
    StopOnly evs ∧ Inv segs k c' := by
  have hx := Omni.exec_star hi.1 (Star.step hs (Star.refl c'))
  obtain ⟨tr, out, -, hp⟩ := Omni.exec_realizes hx
  rw [List.append_nil] at hp
  refine ⟨(stopOnly_append.1 hp.1).1, Omni.exec_conseq hx fun tr out h => ?_, ?_⟩
  · rw [List.append_nil] at h
    exact ⟨(stopOnly_append.1 h.1).2, h.2⟩
  · intro tr c'' hstar
    exact hi.2 _ c'' (Star.step hs hstar)

theorem inv_no_error {c : Silmaril.Process.LPS.Config (isaOf o)} {evs : List Event}
    (hi : Inv segs k c) (hs : SStep segs Probes.spec noFilter c evs .error) : False := by
  cases hi.1 with
  | halt hh => exact hh (Omni.sstep_from_running hs)
  | step _ _ herr =>
    obtain ⟨-, final, h, -⟩ := herr evs hs
    cases h

theorem inv_not_clone {c : Silmaril.Process.LPS.Config (isaOf o)} (hi : Inv segs k c) :
    ¬ ClonePending c := hi.2 [] c (Star.refl c)

/-- **One adapter step** from a state satisfying the invariant is internal and LPS-driven. -/
theorem step_inv {c : Silmaril.Process.LPS.Config (isaOf o)} {a : Act Ev} {s' : St}
    (hi : Inv segs k c) (h : Step (stOf o segs c) a s') :
    a = .tau ∧ ∃ evs c', SStep segs Probes.spec noFilter c evs (.next c') ∧
      s' = stOf o segs c' ∧ Inv segs k c' := by
  cases h with
  | emit hp => cases hp
  | lps _ _ _ hs hm =>
    obtain ⟨hstop, hi'⟩ := inv_next hi hs
    rw [mapEvs_stopOnly hstop] at hm
    cases hm
    exact ⟨rfl, _, _, hs, rfl, hi'⟩
  | unsupported _ _ _ hs hm =>
    rw [mapEvs_stopOnly (inv_next hi hs).1] at hm
    cases hm
  | unmodeled _ _ _ hs => exact (inv_no_error hi hs).elim
  | fault _ _ _ hs => exact (inv_no_error hi hs).elim
  | clone _ _ hh hx hn => exact (inv_not_clone hi ⟨hh, _, hx, hn⟩).elim

/-- **Adapter executions** from a state satisfying the invariant emit nothing. -/
theorem exec_inv {s s' : lps.State} {t : List Ev}
    (hx : MachineSem.Exec lps seqPolicy s t s') :
    ∀ c, s = stOf o segs c → Inv segs k c →
      t = [] ∧ ∃ c', s' = stOf o segs c' ∧ Inv segs k c' := by
  induction hx with
  | refl s => intro c hs hi; exact ⟨rfl, c, hs, hi⟩
  | internal _ hst _ ih =>
    intro c hs hi
    subst hs
    obtain ⟨-, evs, c₁, -, rfl, hi₁⟩ := step_inv hi hst
    exact ih c₁ rfl hi₁
  | ev hst _ _ =>
    intro c hs hi
    subst hs
    obtain ⟨h, -⟩ := step_inv hi hst
    cases h

/-- An `Omni.Exec` configuration has no infinite path of LPS steps. -/
theorem exec_no_path {isa : UserIsa} {sg : List Segment} {c : Silmaril.Process.LPS.Config isa}
    {Q : Omni.Post isa} (hx : Omni.Exec sg Probes.spec noFilter c Q) :
    ∀ g : Nat → Silmaril.Process.LPS.Config isa, g 0 = c →
      (∀ n, ∃ evs, SStep sg Probes.spec noFilter (g n) evs (.next (g (n + 1)))) → False := by
  induction hx with
  | halt hh =>
    intro g h0 hg
    obtain ⟨evs, hs⟩ := hg 0
    rw [h0] at hs
    exact hh (Omni.sstep_from_running hs)
  | step _ _ _ _ ih =>
    intro g h0 hg
    obtain ⟨evs, hs⟩ := hg 0
    rw [h0] at hs
    exact ih evs (g 1) hs (fun n => g (n + 1)) rfl fun n => hg (n + 1)

theorem not_silentDiv {c : Silmaril.Process.LPS.Config (isaOf o)} (hi : Inv segs k c) :
    ¬ MachineSem.SilentDiv lps seqPolicy (stOf o segs c) := by
  rintro ⟨f, h0, hf⟩
  have hall : ∀ n, ∃ c', f n = stOf o segs c' ∧ Inv segs k c' := by
    intro n
    induction n with
    | zero => exact ⟨c, h0, hi⟩
    | succ n ih =>
      obtain ⟨cn, hn, hin⟩ := ih
      obtain ⟨a, -, hst⟩ := hf n
      rw [hn] at hst
      obtain ⟨-, _, c', -, he, hi'⟩ := step_inv hin hst
      exact ⟨c', he, hi'⟩
  choose g hg using hall
  refine exec_no_path hi.1 g (stOf_inj ((hg 0).1.symm.trans h0)) fun n => ?_
  obtain ⟨a, -, hst⟩ := hf n
  rw [(hg n).1] at hst
  obtain ⟨-, evs, c', hs, he, -⟩ := step_inv (hg n).2 hst
  have : c' = g (n + 1) := stOf_inj (he.symm.trans (hg (n + 1)).1)
  exact ⟨evs, this ▸ hs⟩

theorem final_inv {c : Silmaril.Process.LPS.Config (isaOf o)} {st : Stop} (hi : Inv segs k c)
    (h : Final (stOf o segs c) st) : st = .exited (k.toNat % 256).toUInt8 := by
  cases h with
  | undefined _ hb => cases hb
  | exited _ _ hh _ =>
    change c.model.halted = some _ at hh
    cases hi.1 with
    | halt _ hq =>
      obtain ⟨-, final, he, -, hk'⟩ := hq
      cases he
      rw [hh] at hk'
      cases hk'
      rfl
    | step hrun => rw [hrun] at hh; cases hh
  | signaled _ _ hk =>
    change c.model.killedBy = some _ at hk
    cases hi.1 with
    | halt _ hq =>
      obtain ⟨-, final, he, hk', -⟩ := hq
      cases he
      rw [hk] at hk'
      cases hk'
    | step hrun =>
      exfalso
      unfold Silmaril.Process.LPS.Model.killedBy at hk
      unfold Silmaril.Process.LPS.Model.halted at hrun
      rw [hrun] at hk
      split at hk <;> cases hk

theorem final_exists {c : Silmaril.Process.LPS.Config (isaOf o)} (hi : Inv segs k c)
    (hh : c.model.halted ≠ none) : Final (stOf o segs c) (.exited (k.toNat % 256).toUInt8) := by
  cases hi.1 with
  | halt _ hq =>
    obtain ⟨-, final, he, hk, hk'⟩ := hq
    cases he
    exact .exited rfl rfl hk' hk
  | step hrun => exact (hh hrun).elim

theorem not_stuck {c : Silmaril.Process.LPS.Config (isaOf o)} (hi : Inv segs k c) :
    ¬ MachineSem.Stuck lps (stOf o segs c) := by
  rintro ⟨hno, hnf⟩
  cases h : hi.1 with
  | halt hh => exact hnf _ (final_exists hi hh)
  | step hrun hprog =>
    obtain ⟨evs, st, hs⟩ := hprog
    cases st with
    | error => exact inv_no_error hi hs
    | next c' =>
      have hm := mapEvs_stopOnly (inv_next hi hs).1
      exact hno .tau _ (Step.lps (s := stOf o segs c) rfl rfl (inv_not_clone hi) hs hm)

/-- A finite LPS execution from a configuration satisfying the invariant is an adapter
execution that emits nothing. -/
theorem exec_of_star {c c' : Silmaril.Process.LPS.Config (isaOf o)} {tr : List Event}
    (hs : Star segs Probes.spec noFilter c tr c') (hi : Inv segs k c) :
    MachineSem.Exec lps seqPolicy (stOf o segs c) [] (stOf o segs c') ∧ Inv segs k c' := by
  induction hs with
  | refl => exact ⟨.refl _, hi⟩
  | step hss _ ih =>
    obtain ⟨hstop, hi₁⟩ := inv_next hi hss
    obtain ⟨hx, hi'⟩ := ih hi₁
    refine ⟨.internal (a := .tau) trivial ?_ hx, hi'⟩
    exact Step.lps (s := stOf o segs _) rfl rfl (inv_not_clone hi) hss (mapEvs_stopOnly hstop)

/-! ## The runs -/

theorem load_inv {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) {s : St}
    (hl : lps.load snap s) :
    ∃ o, ∃ c : Silmaril.Process.LPS.Config (isaOf o), s = stOf o snap.image.segments c ∧
      Inv snap.image.segments k c := by
  obtain ⟨o, limit, en, inp, ha, rfl⟩ := hl
  exact ⟨o, _, rfl, h.exec o limit en inp ha, h.noClone o limit en inp ha⟩

theorem runs_eq {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) (b : Beh Ev)
    (hb : lps.Run seqPolicy snap b) : b = .done [] (.exited (k.toNat % 256).toUInt8) := by
  cases hb with
  | final hl hx hf =>
    obtain ⟨o, c, rfl, hi⟩ := load_inv h hl
    obtain ⟨rfl, c', rfl, hi'⟩ := exec_inv hx c rfl hi
    rw [final_inv hi' hf]
  | clone hl hx hc _ =>
    obtain ⟨o, c, rfl, hi⟩ := load_inv h hl
    obtain ⟨-, c', rfl, hi'⟩ := exec_inv hx c rfl hi
    obtain ⟨ha, -⟩ := step_inv hi' hc
    cases ha
  | stuck hl hx hst =>
    obtain ⟨o, c, rfl, hi⟩ := load_inv h hl
    obtain ⟨-, c', rfl, hi'⟩ := exec_inv hx c rfl hi
    exact (not_stuck hi' hst).elim
  | blocked hl hx hw =>
    obtain ⟨o, c, rfl, hi⟩ := load_inv h hl
    obtain ⟨-, c', rfl, hi'⟩ := exec_inv hx c rfl hi
    obtain ⟨-, ⟨e, s'', -, hst⟩, -⟩ := hw
    obtain ⟨ha, -⟩ := step_inv hi' hst
    cases ha
  | spins hl hx hd =>
    obtain ⟨o, c, rfl, hi⟩ := load_inv h hl
    obtain ⟨-, c', rfl, hi'⟩ := exec_inv hx c rfl hi
    exact (not_silentDiv hi' hd).elim
  | reactive f hf =>
    obtain ⟨s, s', hl, hx⟩ := hf 1
    obtain ⟨o, c, rfl, hi⟩ := load_inv h hl
    obtain ⟨ht, -⟩ := exec_inv hx c rfl hi
    simp at ht
  | noInit hn =>
    obtain ⟨o, en, inp, ha⟩ := h.launch
    exact (hn _ ⟨o, 0, en, inp, ha, rfl⟩).elim

theorem run_exists {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) :
    lps.Run seqPolicy snap (.done [] (.exited (k.toNat % 256).toUInt8)) := by
  obtain ⟨o, en, inp, ha⟩ := h.launch
  have hi : Inv snap.image.segments k (X86Launch.init (isaOf o) snap en 0 inp) :=
    ⟨h.exec o 0 en inp ha, h.noClone o 0 en inp ha⟩
  obtain ⟨tr, out, hm, hp⟩ := Omni.exec_realizes hi.1
  obtain ⟨-, final, rfl, -, hk⟩ := hp
  obtain ⟨hs, hh⟩ := Omni.mexec_halt_star hm
  obtain ⟨hx, hi'⟩ := exec_of_star hs hi
  exact .final (s := stOf o snap.image.segments _) ⟨o, 0, en, inp, ha, rfl⟩ hx (final_exists hi' hh)

/-! ## No task creation along a unique-successor chain -/

theorem noClone_halted {isa : UserIsa} {sg : List Segment} {c : Silmaril.Process.LPS.Config isa}
    (hh : c.model.halted ≠ none) : NoCloneFrom sg c := by
  intro tr c' hs
  cases hs with
  | refl => exact fun h => hh h.1
  | step hss => exact (hh (Omni.sstep_from_running hss)).elim

theorem noClone_unique {isa : UserIsa} {sg : List Segment} {c c' : Silmaril.Process.LPS.Config isa}
    {events : List Event} (hc : ¬ ClonePending c)
    (succ : ∀ evs t, SStep sg Probes.spec noFilter c evs t ↔ evs = events ∧ t = .next c')
    (rest : NoCloneFrom sg c') : NoCloneFrom sg c := by
  intro tr c'' hs
  cases hs with
  | refl => exact hc
  | step hss hrest =>
    obtain ⟨-, ht⟩ := (succ _ _).1 hss
    cases ht
    exact rest _ _ hrest

open Silmaril.Process.LPS.Probes in
theorem noClone_instr (P : Probe) (oracle : Oracle) [Probe.Checked P] {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : NoCloneFrom P.segs (P.ocfg oracle core' none counter model)) :
    NoCloneFrom P.segs (P.ocfg oracle core none counter model) :=
  noClone_unique (fun ⟨_, _, hx, _⟩ => by cases hx)
    (P.osstep_instr_iff oracle running lazy rip fits two notSyscall decoded exec) rest

open Silmaril.Process.LPS.Probes in
theorem noClone_trap (P : Probe) (oracle : Oracle) [Probe.Checked P] {off : Nat}
    {core : Silmaril.X86.State} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : NoCloneFrom P.segs (P.ocfg oracle (Probe.complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model)) :
    NoCloneFrom P.segs (P.ocfg oracle core none counter model) :=
  noClone_unique (fun ⟨_, _, hx, _⟩ => by cases hx)
    (P.osstep_trap_iff oracle running lazy rip two isSyscall) rest

open Silmaril.Process.LPS.Probes in
theorem noClone_exit (P : Probe) (oracle : Oracle) {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} (number : n = 60)
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false) :
    NoCloneFrom P.segs (P.ocfg oracle core (some n) counter model) := by
  subst number
  refine noClone_unique (fun ⟨_, x8, hx, hn⟩ => ?_) (P.osstep_exit_iff oracle running clear)
    (noClone_halted (by simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted]))
  cases hx
  exact Bool.noConfusion hn

end Silmaril.Proofs.Containers.Lps
