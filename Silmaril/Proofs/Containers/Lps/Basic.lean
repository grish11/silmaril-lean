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

/-! ## Container events of a trace -/

theorem mapEvs_nil : mapEvs [] = some [] := rfl

theorem mapEvs_cons (e : Event) (tr : List Event) :
    mapEvs (e :: tr) = (mapEv e).bind fun x => (mapEvs tr).map (x ++ ·) := by
  unfold mapEvs
  simp only [List.mapM_cons]
  cases mapEv e <;> cases List.mapM mapEv tr <;> rfl

theorem mapEvs_append : ∀ (a b : List Event),
    mapEvs (a ++ b) = (mapEvs a).bind fun x => (mapEvs b).map (x ++ ·)
  | [], b => by
    rw [List.nil_append, mapEvs_nil]
    cases mapEvs b <;> rfl
  | e :: a, b => by
    rw [List.cons_append, mapEvs_cons, mapEvs_append a b, mapEvs_cons]
    cases mapEv e <;> cases mapEvs a <;> cases mapEvs b <;> simp

theorem mapEvs_append_some {a b : List Event} {u : List Ev} (h : mapEvs (a ++ b) = some u) :
    ∃ x y, mapEvs a = some x ∧ mapEvs b = some y ∧ u = x ++ y := by
  rw [mapEvs_append] at h
  cases ha : mapEvs a <;> cases hb : mapEvs b <;> simp_all

theorem mapEvs_append_none {a b : List Event} (h : mapEvs a = none) : mapEvs (a ++ b) = none := by
  rw [mapEvs_append, h]
  rfl

/-- Octets written to standard output, then an exit: one standard-output event per octet. -/
theorem mapEvs_stdout_exit (c : Word) (fs : Fs.FileSystem) : ∀ ds : List Byte,
    mapEvs (ds.map (.writeEv 1) ++ [.exitEv c fs]) = some (ds.map fun b => .stdout [UInt8.ofBitVec b])
  | [] => rfl
  | d :: ds => by
    rw [List.map_cons, List.cons_append, mapEvs_cons, mapEvs_stdout_exit c fs ds]
    rfl

/-! ## The invariant -/

variable {sp : Sys SyscallEffect} {o : Oracle} {segs : List Segment} {k : Word} {w : List Ev}
  {G : List Ev → Word → Prop}

/-- **The invariant**: every maximal LPS execution from `c` has supported events and halts,
unkilled, with a status `k` such that `G` holds of the events `t` already emitted, `p` still
pending, and its own container events; and no configuration reachable from `c` is about to
create a task. -/
def Inv (sp : Sys SyscallEffect) (segs : List Segment) (G : List Ev → Word → Prop) (t : List Ev)
    (c : Silmaril.Process.LPS.Config (isaOf o)) (p : List Ev) : Prop :=
  Omni.Exec segs sp noFilter c (EvPost G (t ++ p)) ∧ NoCloneFromWith sp segs c

/-- The adapter state of a configuration with pending events `p` and no undefined behaviour. -/
def stAt (o : Oracle) (segs : List Segment) (c : Silmaril.Process.LPS.Config (isaOf o))
    (p : List Ev) : St :=
  ⟨o, segs, c, p, none⟩

theorem stAt_inj {c₁ c₂ : Silmaril.Process.LPS.Config (isaOf o)} {p₁ p₂ : List Ev}
    (h : stAt o segs c₁ p₁ = stAt o segs c₂ p₂) : c₁ = c₂ ∧ p₁ = p₂ := by
  unfold stAt at h
  cases h
  exact ⟨rfl, rfl⟩

/-- What is emitted and pending extends to events `G` accepts. -/
theorem inv_realizes {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs G t c p) : ∃ es k, G (t ++ p ++ es) k := by
  obtain ⟨tr, out, -, es, -, final, -, -, k, -, hg⟩ := Omni.exec_realizes hi.1
  exact ⟨es, k, hg⟩

theorem inv_next {t p : List Ev} {c c' : Silmaril.Process.LPS.Config (isaOf o)} {evs : List Event}
    (hi : Inv sp segs G t c p) (hs : SStep segs sp noFilter c evs (.next c')) :
    ∃ es, mapEvs evs = some es ∧ Inv sp segs G t c' (p ++ es) := by
  have hx := Omni.exec_star hi.1 (Star.step hs (Star.refl c'))
  obtain ⟨tr, out, -, u, hu, -⟩ := Omni.exec_realizes hx
  rw [List.append_nil] at hu
  obtain ⟨es, -, hes, -, -⟩ := mapEvs_append_some hu
  refine ⟨es, hes, Omni.exec_conseq hx fun tr out h => ?_, ?_⟩
  · rw [List.append_nil] at h
    obtain ⟨u, hu, final, hf, hk, k, hh, hg⟩ := h
    obtain ⟨x, y, hx, hy, rfl⟩ := mapEvs_append_some hu
    rw [hes] at hx
    cases hx
    exact ⟨y, hy, final, hf, hk, k, hh, by simpa [List.append_assoc] using hg⟩
  · intro tr c'' hstar
    exact hi.2 _ c'' (Star.step hs hstar)

theorem inv_unsupported {t p : List Ev} {c c' : Silmaril.Process.LPS.Config (isaOf o)}
    {evs : List Event} (hi : Inv sp segs G t c p)
    (hs : SStep segs sp noFilter c evs (.next c')) (hm : mapEvs evs = none) : False := by
  obtain ⟨es, he, -⟩ := inv_next hi hs
  rw [hm] at he
  cases he

theorem inv_no_error {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)} {evs : List Event}
    (hi : Inv sp segs G t c p) (hs : SStep segs sp noFilter c evs .error) : False := by
  cases hi.1 with
  | halt hh => exact hh (Omni.sstep_from_running hs)
  | step _ _ herr =>
    obtain ⟨-, -, final, h, -⟩ := herr evs hs
    cases h

theorem inv_not_clone {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs G t c p) : ¬ ClonePending c := hi.2 [] c (Star.refl c)

theorem inv_emit {t p : List Ev} {e : Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs G t c (e :: p)) : Inv sp segs G (t ++ [e]) c p := by
  refine ⟨Omni.exec_conseq hi.1 fun tr out h => ?_, hi.2⟩
  simpa [List.append_assoc] using h

/-- **One adapter step** from a state satisfying the invariant: it emits the first pending event,
or, with nothing pending, it is an internal LPS step with supported events. -/
theorem step_inv {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)} {a : Act Ev} {s' : St}
    (hi : Inv sp segs G t c p) (h : Step sp (stAt o segs c p) a s') :
    (∃ e p', p = e :: p' ∧ a = .ev e ∧ s' = stAt o segs c p' ∧ Inv sp segs G (t ++ [e]) c p') ∨
    (p = [] ∧ a = .tau ∧ ∃ evs c' es, SStep segs sp noFilter c evs (.next c') ∧
      mapEvs evs = some es ∧ s' = stAt o segs c' es ∧ Inv sp segs G t c' es) := by
  cases h with
  | emit hp =>
    change p = _ at hp
    subst hp
    exact .inl ⟨_, _, rfl, rfl, rfl, inv_emit hi⟩
  | lps hp _ _ hs hm =>
    change p = [] at hp
    subst hp
    obtain ⟨es, he, hi'⟩ := inv_next hi hs
    rw [he] at hm
    cases hm
    exact .inr ⟨rfl, rfl, _, _, _, hs, he, rfl, by simpa using hi'⟩
  | unsupported _ _ _ hs hm => exact (inv_unsupported hi hs hm).elim
  | unmodeled _ _ _ hs => exact (inv_no_error hi hs).elim
  | fault _ _ _ hs => exact (inv_no_error hi hs).elim
  | clone _ _ hh hx hn => exact (inv_not_clone hi ⟨hh, _, hx, hn⟩).elim

/-- **Adapter executions** from a state satisfying the invariant keep it, with the emitted events
appended. -/
theorem exec_inv {s s' : (lpsWith sp).State} {u : List Ev}
    (hx : MachineSem.Exec (lpsWith sp) seqPolicy s u s') :
    ∀ t c p, s = stAt o segs c p → Inv sp segs G t c p →
      ∃ c' p', s' = stAt o segs c' p' ∧ Inv sp segs G (t ++ u) c' p' := by
  induction hx with
  | refl s => intro t c p hs hi; exact ⟨c, p, hs, by simpa using hi⟩
  | internal _ hst _ ih =>
    intro t c p hs hi
    subst hs
    rcases step_inv hi hst with ⟨e, p', -, rfl, -, -⟩ | ⟨-, -, evs, c₁, es, -, -, rfl, hi₁⟩
    · contradiction
    · exact ih t c₁ es rfl hi₁
  | ev hst _ ih =>
    intro t c p hs hi
    subst hs
    rcases step_inv hi hst with ⟨e, p', -, he, rfl, hi₁⟩ | ⟨-, h, -⟩
    · cases he
      obtain ⟨c', p'', h', hi'⟩ := ih _ c p' rfl hi₁
      exact ⟨c', p'', h', by simpa [List.append_assoc] using hi'⟩
    · cases h

/-- An `Omni.Exec` configuration has no infinite path of LPS steps. -/
theorem exec_no_path {isa : UserIsa} {sg : List Segment} {c : Silmaril.Process.LPS.Config isa}
    {Q : Omni.Post isa} (hx : Omni.Exec sg sp noFilter c Q) :
    ∀ g : Nat → Silmaril.Process.LPS.Config isa, g 0 = c →
      (∀ n, ∃ evs, SStep sg sp noFilter (g n) evs (.next (g (n + 1)))) → False := by
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

theorem not_silentDiv {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs G t c p) : ¬ MachineSem.SilentDiv (lpsWith sp) seqPolicy (stAt o segs c p) := by
  rintro ⟨f, h0, hf⟩
  have hall : ∀ n, ∃ cp : Silmaril.Process.LPS.Config (isaOf o) × List Ev,
      f n = stAt o segs cp.1 cp.2 ∧ Inv sp segs G t cp.1 cp.2 := by
    intro n
    induction n with
    | zero => exact ⟨(c, p), h0, hi⟩
    | succ n ih =>
      obtain ⟨⟨cn, pn⟩, hn, hin⟩ := ih
      obtain ⟨a, ha, hst⟩ := hf n
      rw [hn] at hst
      rcases step_inv hin hst with ⟨e, p', -, rfl, -, -⟩ | ⟨-, -, evs, c', es, -, -, he, hi'⟩
      · exact ha.elim
      · exact ⟨(c', es), he, hi'⟩
  choose g hg using hall
  refine exec_no_path hi.1 (fun n => (g n).1)
    (stAt_inj ((hg 0).1.symm.trans h0)).1 fun n => ?_
  obtain ⟨a, ha, hst⟩ := hf n
  rw [(hg n).1] at hst
  rcases step_inv (hg n).2 hst with ⟨e, p', -, rfl, -, -⟩ | ⟨-, -, evs, c', es, hs, -, he, -⟩
  · exact ha.elim
  · have : c' = (g (n + 1)).1 := (stAt_inj (he.symm.trans (hg (n + 1)).1)).1
    exact ⟨evs, this ▸ hs⟩

theorem final_inv {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)} {st : Stop}
    (hi : Inv sp segs G t c p) (h : Final (stAt o segs c p) st) :
    p = [] ∧ ∃ k, st = .exited (k.toNat % 256).toUInt8 ∧ G t k := by
  cases h with
  | undefined _ hb => cases hb
  | exited hp _ hh _ =>
    change p = [] at hp
    change c.model.halted = some _ at hh
    subst hp
    cases hi.1 with
    | halt _ hq =>
      obtain ⟨es, hes, final, he, -, k, hk', hg⟩ := hq
      cases he
      cases hes
      rw [hh] at hk'
      cases hk'
      exact ⟨rfl, _, rfl, by simpa using hg⟩
    | step hrun => rw [hrun] at hh; cases hh
  | signaled _ _ hk =>
    change c.model.killedBy = some _ at hk
    cases hi.1 with
    | halt _ hq =>
      obtain ⟨-, -, final, he, hk', -⟩ := hq
      cases he
      rw [hk] at hk'
      cases hk'
    | step hrun =>
      exfalso
      unfold Silmaril.Process.LPS.Model.killedBy at hk
      unfold Silmaril.Process.LPS.Model.halted at hrun
      rw [hrun] at hk
      split at hk <;> cases hk

theorem final_exists {t : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs G t c []) (hh : c.model.halted ≠ none) :
    ∃ st, Final (stAt o segs c []) st := by
  cases hi.1 with
  | halt _ hq =>
    obtain ⟨-, -, final, he, hk, k, hk', -⟩ := hq
    cases he
    exact ⟨_, .exited rfl rfl hk' hk⟩
  | step hrun => exact (hh hrun).elim

theorem not_stuck {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs G t c p) : ¬ MachineSem.Stuck (lpsWith sp) (stAt o segs c p) := by
  rintro ⟨hno, hnf⟩
  cases p with
  | cons e p => exact hno (.ev e) _ (Step.emit (s := stAt o segs c (e :: p)) rfl)
  | nil =>
    cases h : hi.1 with
    | halt hh =>
      obtain ⟨st, hf⟩ := final_exists hi hh
      exact hnf _ hf
    | step hrun hprog =>
      obtain ⟨evs, st, hs⟩ := hprog
      cases st with
      | error => exact inv_no_error hi hs
      | next c' =>
        cases hm : mapEvs evs with
        | none => exact inv_unsupported hi hs hm
        | some es =>
          exact hno .tau _ (Step.lps (s := stAt o segs c []) rfl rfl (inv_not_clone hi) hs hm)

theorem not_waiting {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hw : ∀ u k e, G u k → e ∈ u → e.isInput = false) (hi : Inv sp segs G t c p) :
    ¬ MachineSem.Waiting (lpsWith sp) (stAt o segs c p) := by
  rintro ⟨-, ⟨e, s', hin, hst⟩, -⟩
  rcases step_inv hi hst with ⟨e', p', rfl, he, -, -⟩ | ⟨-, h, -⟩
  · cases he
    obtain ⟨es, k, hg⟩ := inv_realizes hi
    have hmem : e ∈ t ++ e :: p' ++ es :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))
    exact Bool.false_ne_true ((hw _ _ _ hg hmem).symm.trans hin)
  · cases h

/-! ## From LPS executions to adapter executions -/

/-- Emitting the pending events. -/
theorem exec_emits {c : Silmaril.Process.LPS.Config (isaOf o)} {u : List Ev} {s : St} :
    ∀ es : List Ev, MachineSem.Exec (lpsWith sp) seqPolicy (stAt o segs c []) u s →
      MachineSem.Exec (lpsWith sp) seqPolicy (stAt o segs c es) (es ++ u) s
  | [], h => h
  | e :: es, h => .ev (Step.emit (s := stAt o segs c (e :: es)) rfl) (exec_emits es h)

/-- A finite LPS execution with supported events and no task creation is an adapter execution
that emits its container events. -/
theorem exec_of_star {c c' : Silmaril.Process.LPS.Config (isaOf o)} {tr : List Event}
    (hs : Star segs sp noFilter c tr c') (hn : NoCloneFromWith sp segs c) :
    ∀ {u}, mapEvs tr = some u →
      MachineSem.Exec (lpsWith sp) seqPolicy (stAt o segs c []) u (stAt o segs c' []) := by
  induction hs with
  | refl => intro u hu; cases hu; exact .refl _
  | step hss hrest ih =>
    intro u hu
    obtain ⟨es, u', hes, hu', rfl⟩ := mapEvs_append_some hu
    have hc : ¬ ClonePending _ := hn [] _ (Star.refl _)
    refine .internal (a := .tau) trivial
      (Step.lps (s := stAt o segs _ []) (es := es) rfl rfl hc hss hes) ?_
    exact exec_emits es (ih (fun tr c'' h => hn _ c'' (Star.step hss h)) hu')

/-! ## The runs: general soundness -/

theorem load_invG {snap : X86Launch.Snapshot} (h : Sound sp snap G) {s : St}
    (hl : (lpsWith sp).load snap s) :
    ∃ o, ∃ c : Silmaril.Process.LPS.Config (isaOf o), s = stAt o snap.image.segments c [] ∧
      Inv sp snap.image.segments G [] c [] := by
  obtain ⟨o, limit, en, inp, ha, rfl⟩ := hl
  exact ⟨o, _, rfl, h.exec o limit en inp ha, h.noClone o limit en inp ha⟩

/-- **General soundness**: under `Sound sp snap G`, no run has undefined behaviour, and every run
that exits with status `c` has events `t` with `G t k` for a status word `k` with `c = k mod 256`.
Blocking, divergence and infinite runs are not excluded (partial correctness). -/
theorem runs_sound {snap : X86Launch.Snapshot} (h : Sound sp snap G) (b : Beh Ev)
    (hb : (lpsWith sp).Run seqPolicy snap b) :
    Spec.noUB b ∧ ∀ t c, b = .done t (.exited c) → ∃ k, c = (k.toNat % 256).toUInt8 ∧ G t k := by
  cases hb with
  | final hl hx hf =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG h hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    obtain ⟨rfl, k, rfl, hg⟩ := final_inv hi' hf
    refine ⟨trivial, fun t c he => ?_⟩
    cases he
    exact ⟨k, rfl, by simpa using hg⟩
  | clone hl hx hc _ =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG h hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    rcases step_inv hi' hc with h₁ | h₁
    · obtain ⟨_, _, _, hact, _⟩ := h₁
      cases hact
    · obtain ⟨_, hact, _⟩ := h₁
      cases hact
  | stuck hl hx hst =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG h hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    exact (not_stuck hi' hst).elim
  | blocked => exact ⟨trivial, fun _ _ he => nomatch he⟩
  | spins => exact ⟨trivial, fun _ _ he => nomatch he⟩
  | reactive => exact ⟨trivial, fun _ _ he => nomatch he⟩
  | noInit hn =>
    obtain ⟨o, en, inp, ha⟩ := h.launch
    exact (hn _ ⟨o, 0, en, inp, ha, rfl⟩).elim

/-! ## The runs of programs with bounded output -/

/-- The judgment of `Emits`: a prefix of `w`, status `k`. -/
def prefixG (w : List Ev) (k : Word) : List Ev → Word → Prop := fun u c => u <+: w ∧ c = k

theorem evPost_of_prefixPost {o : Oracle} {pre : List Ev} {tr : List Event}
    {out : Omni.Outcome (isaOf o)} (h : PrefixPost w k pre tr out) :
    EvPost (prefixG w k) pre tr out := by
  obtain ⟨⟨es, hes, hp⟩, final, hf, hk, hh⟩ := h
  exact ⟨es, hes, final, hf, hk, k, hh, hp, rfl⟩

theorem sound_of_emits {snap : X86Launch.Snapshot} (h : Emits snap k w) :
    Sound Probes.spec snap (prefixG w k) where
  exec o limit en inp ha :=
    Omni.exec_conseq (h.exec o limit en inp ha) fun _ _ hp => evPost_of_prefixPost hp
  noClone := h.noClone
  launch := h.launch

theorem inv_prefix {t p : List Ev} {c : Silmaril.Process.LPS.Config (isaOf o)}
    (hi : Inv sp segs (prefixG w k) t c p) : t ++ p <+: w := by
  obtain ⟨es, k, hp, -⟩ := inv_realizes hi
  exact (List.prefix_append _ _).trans hp

theorem runs_prefix {snap : X86Launch.Snapshot} (h : Emits snap k w) (b : Beh Ev)
    (hb : lps.Run seqPolicy snap b) : ∃ t, t <+: w ∧ b = .done t (.exited (k.toNat % 256).toUInt8) := by
  have hs := sound_of_emits h
  have hw : ∀ u k' e, prefixG w k u k' → e ∈ u → e.isInput = false :=
    fun u k' e hg he => h.outputs e (hg.1.subset he)
  cases hb with
  | final hl hx hf =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG hs hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    obtain ⟨rfl, k', rfl, hp, rfl⟩ := final_inv hi' hf
    exact ⟨_, by simpa using hp, rfl⟩
  | clone hl hx hc _ =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG hs hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    rcases step_inv hi' hc with h₁ | h₁
    · obtain ⟨_, _, _, hact, _⟩ := h₁
      cases hact
    · obtain ⟨_, hact, _⟩ := h₁
      cases hact
  | stuck hl hx hst =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG hs hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    exact (not_stuck hi' hst).elim
  | blocked hl hx hwt =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG hs hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    exact (not_waiting hw hi' hwt).elim
  | spins hl hx hd =>
    obtain ⟨o, c, rfl, hi⟩ := load_invG hs hl
    obtain ⟨c', p', rfl, hi'⟩ := exec_inv hx [] c [] rfl hi
    exact (not_silentDiv hi' hd).elim
  | reactive f hf =>
    obtain ⟨s, s', hl, hx⟩ := hf (w.length + 1)
    obtain ⟨o, c, rfl, hi⟩ := load_invG hs hl
    obtain ⟨c', p', -, hi'⟩ := exec_inv hx [] c [] rfl hi
    have hlen := (inv_prefix hi').length_le
    simp at hlen
    omega
  | noInit hn =>
    obtain ⟨o, en, inp, ha⟩ := h.launch
    exact (hn _ ⟨o, 0, en, inp, ha, rfl⟩).elim

/-- **A chosen LPS execution is a run**: a finite execution of an admissible launch to a halted,
unkilled configuration, with supported events and no task creation, is the run that emits their
container events. -/
theorem run_of_starWith {snap : X86Launch.Snapshot} {o : Oracle} {limit : Int}
    {en : ExecEntry} {inp : ProcInput} (ha : Problems.CoreutilsLite.Admissible o snap en inp)
    {tr : List Event} {c' : Silmaril.Process.LPS.Config (isaOf o)} {u : List Ev} {code : Word}
    (hn : NoCloneFromWith sp snap.image.segments (X86Launch.init (isaOf o) snap en limit inp))
    (hs : Star snap.image.segments sp noFilter
      (X86Launch.init (isaOf o) snap en limit inp) tr c')
    (hu : mapEvs tr = some u) (hh : c'.model.halted = some code) (hk : c'.model.killedBy = none) :
    (lpsWith sp).Run seqPolicy snap (.done u (.exited (code.toNat % 256).toUInt8)) :=
  .final (s := stAt o snap.image.segments _ []) ⟨o, limit, en, inp, ha, rfl⟩
    (exec_of_star hs hn hu) (.exited rfl rfl hh hk)

theorem run_of_star {snap : X86Launch.Snapshot} (h : Emits snap k w) {o : Oracle} {limit : Int}
    {en : ExecEntry} {inp : ProcInput} (ha : Problems.CoreutilsLite.Admissible o snap en inp)
    {tr : List Event} {c' : Silmaril.Process.LPS.Config (isaOf o)} {u : List Ev} {code : Word}
    (hs : Star snap.image.segments Probes.spec noFilter
      (X86Launch.init (isaOf o) snap en limit inp) tr c')
    (hu : mapEvs tr = some u) (hh : c'.model.halted = some code) (hk : c'.model.killedBy = none) :
    lps.Run seqPolicy snap (.done u (.exited (code.toNat % 256).toUInt8)) :=
  run_of_starWith ha (h.noClone o limit en inp ha) hs hu hh hk

theorem run_exists {snap : X86Launch.Snapshot} (h : Emits snap k w) :
    ∃ t, t <+: w ∧ lps.Run seqPolicy snap (.done t (.exited (k.toNat % 256).toUInt8)) := by
  obtain ⟨o, en, inp, ha⟩ := h.launch
  obtain ⟨tr, out, hm, ⟨u, hu, hp⟩, final, rfl, hk, hh⟩ := Omni.exec_realizes (h.exec o 0 en inp ha)
  obtain ⟨hs, -⟩ := Omni.mexec_halt_star hm
  exact ⟨u, hp, run_of_star h ha hs hu hh hk⟩

/-! ## Programs that only exit -/

theorem prefixPost_of_post {tr : List Event} {out : Omni.Outcome (isaOf o)} (h : Post k tr out) :
    PrefixPost [] k [] tr out :=
  ⟨⟨[], mapEvs_stopOnly h.1, List.prefix_refl _⟩, h.2⟩

theorem emits_of_exitOnly {snap : X86Launch.Snapshot} (h : ExitOnly snap k) : Emits snap k [] where
  exec o limit en inp ha := Omni.exec_conseq (h.exec o limit en inp ha) fun _ _ hp => prefixPost_of_post hp
  noClone := h.noClone
  launch := h.launch
  outputs _ he := nomatch he

theorem runs_eq {snap : X86Launch.Snapshot} (h : ExitOnly snap k) (b : Beh Ev)
    (hb : lps.Run seqPolicy snap b) : b = .done [] (.exited (k.toNat % 256).toUInt8) := by
  obtain ⟨t, ht, rfl⟩ := runs_prefix (emits_of_exitOnly h) b hb
  rw [List.eq_nil_of_prefix_nil ht]

theorem run_exists_exit {snap : X86Launch.Snapshot} (h : ExitOnly snap k) :
    lps.Run seqPolicy snap (.done [] (.exited (k.toNat % 256).toUInt8)) := by
  obtain ⟨t, ht, hr⟩ := run_exists (emits_of_exitOnly h)
  rwa [List.eq_nil_of_prefix_nil ht] at hr

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

theorem noClone_successors {isa : UserIsa} {sg : List Segment} {c : Silmaril.Process.LPS.Config isa}
    (hc : ¬ ClonePending c)
    (rest : ∀ evs c', SStep sg Probes.spec noFilter c evs (.next c') → NoCloneFrom sg c') :
    NoCloneFrom sg c := by
  intro tr c'' hs
  cases hs with
  | refl => exact hc
  | step hss hrest => exact rest _ _ hss _ _ hrest

open Silmaril.Process.LPS.Probes in
theorem noClone_write (P : Probe) (oracle : Oracle) [Probe.Checked P] {core : Silmaril.X86.State}
    {n : Word} {counter : Nat} {model : Silmaril.Process.LPS.Model} {off count : Nat} {ch : Word}
    (number : n = 1) (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count)
    (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (rest : ∀ ds, Probe.WritePrefix ((P.bytes.drop off).take count) ds →
      NoCloneFrom P.segs (P.ocfg oracle (Probe.resume core (lenWord ds)) none counter model)) :
    NoCloneFrom P.segs (P.ocfg oracle core (some n) counter model) := by
  subst number
  refine noClone_successors (fun ⟨_, x8, hx, hn⟩ => ?_) fun evs c' hs => ?_
  · cases hx
    exact Bool.noConfusion hn
  · obtain ⟨ds, ⟨hw, -⟩, -, ht⟩ := (P.osstep_write_iff oracle rfl running lazy lookup nonzero buffer
      modeled nonzeroCount clear clamp clampWord fits nonempty evs _).1 hs
    cases ht
    exact rest ds hw

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
