module

public import Silmaril.Wasm.Abstract.NodeBridge.Defs
public import Silmaril.Wasm.Game.Machine.Thms

/-!
# Core 3.0 instances seen through the Core host interface (proofs)

**Frames.** A Core step from a configuration without locals keeps its frame (`step_frame_eq`:
`local.set` needs a local), so every labelled run from an invocation stays in the empty frame
(`evRun_frame_eq`).

**Runs.** A labelled Core run is a run ending at an event (`EvRunE`) followed by a silent run
(`evRun_iff`). Against `instHost I`, a silent step is a host-free step (`hevNone_iff`), so a silent
run from a thread configuration is a host-free run of the single-threaded machine
(`reach_silent`, `silent_reach`).

**Segments.** One import call of the instance, a `ucall` and the `uret` answering it, is a silent
Core run to the callout followed by the host event that it views (`seg_fwd`, `seg_bwd`). By
induction on the import log, the instance runs along `callMoves c` are the event-ended Core runs
whose events view `c` (`path_calls_fwd`, `path_calls_bwd`). The four kinds of activation (returns,
divergence, pending calls, productive runs) follow, hence the triple equality
(`instTripleS_eq_viewTriple`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeBridge

open Silmaril Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract Silmaril.Wasm.Abstract.NodeBridge
open Silmaril.Wasm.Numerics (Profile)

/-! ## Frames -/

section Frames

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A Core step from a frame without locals keeps the frame. -/
theorem step_frame_eq {c c' : Config H} (h : Step P host c c') :
    c.frame.locals = [] → c'.frame = c.frame := by
  induction h with
  | «variable» h =>
    intro hl
    cases h with
    | localSet hx => simp_all
    | _ => rfl
  | table h => intro _; cases h <;> rfl
  | memory h => intro _; cases h <;> rfl
  | reference h => intro _; cases h <;> rfl
  | aggregate h => intro _; cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => intro _; rfl

/-- A labelled step from a frame without locals keeps the frame. -/
theorem hevStep_frame_eq {c c' : Config H} {o : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c o c') (hl : c.frame.locals = []) : c'.frame = c.frame := by
  cases o with
  | none =>
    rcases h with h | ⟨rfl, -⟩
    · exact step_frame_eq h hl
    · rfl
  | some e =>
    obtain ⟨_, _, -, -, -, rfl⟩ := h
    rfl

/-- A labelled run from a frame without locals keeps the frame. -/
theorem evRun_frame_eq {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') (hl : c.frame.locals = []) : c'.frame = c.frame := by
  induction h with
  | refl => rfl
  | silent hs _ ih =>
    have he := hevStep_frame_eq hs hl
    rw [ih (he ▸ hl), he]
  | event hs _ ih =>
    have he := hevStep_frame_eq hs hl
    rw [ih (he ▸ hl), he]

/-- **Every labelled run of an invocation stays in the empty frame.** -/
theorem evRun_invoke_frame {s : Store H} {a : Nat} {vs : List Val} {c : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host (invoke s a vs) cs c) :
    c.frame = {} :=
  evRun_frame_eq h rfl

end Frames

/-! ## Labelled runs cut at their last event -/

section Runs

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A labelled run ending at its last event (or empty). -/
def EvRunE (P : Profile) (host : HostSemantics H) :
    Config H → List (Call (wasmHostSig H)) → Config H → Prop
  | c, [], c' => c' = c
  | c, e :: cs, c' => ∃ c₁ c₂, Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c₁ ∧
      HEvStep P host c₁ (some e) c₂ ∧ EvRunE P host c₂ cs c'

theorem evRun_nil_iff {c c' : Config H} :
    EvRun P host c [] c' ↔ Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c' := by
  constructor
  · intro h
    generalize hcs : ([] : List (Call (wasmHostSig H))) = cs at h
    induction h with
    | refl => exact .refl
    | silent hs _ ih => exact .head hs (ih hcs)
    | event _ _ _ => cases hcs
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl _
    | head hs _ ih => exact .silent hs ih

theorem evRun_cons_iff {c c' : Config H} {e : Call (wasmHostSig H)}
    {cs : List (Call (wasmHostSig H))} :
    EvRun P host c (e :: cs) c' ↔ ∃ c₁ c₂,
      Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c₁ ∧
        HEvStep P host c₁ (some e) c₂ ∧ EvRun P host c₂ cs c' := by
  constructor
  · intro h
    generalize hcs : e :: cs = l at h
    induction h with
    | refl => cases hcs
    | silent hs _ ih =>
      obtain ⟨c₁, c₂, h₁, h₂, h₃⟩ := ih hcs
      exact ⟨c₁, c₂, .head hs h₁, h₂, h₃⟩
    | event hs h _ =>
      cases hcs
      exact ⟨_, _, .refl, hs, h⟩
  · rintro ⟨c₁, c₂, h₁, h₂, h₃⟩
    induction h₁ using Relation.ReflTransGen.head_induction_on with
    | refl => exact .event h₂ h₃
    | head hs _ ih => exact .silent hs ih

/-- **A labelled run is a run ending at its last event, then a silent run.** -/
theorem evRun_iff {c c'' : Config H} {cs : List (Call (wasmHostSig H))} :
    EvRun P host c cs c'' ↔ ∃ c', EvRunE P host c cs c' ∧
      Relation.ReflTransGen (fun a b => HEvStep P host a none b) c' c'' := by
  induction cs generalizing c with
  | nil =>
    rw [evRun_nil_iff]
    exact ⟨fun h => ⟨c, rfl, h⟩, fun ⟨_, h₁, h₂⟩ => h₁ ▸ h₂⟩
  | cons e cs ih =>
    rw [evRun_cons_iff]
    constructor
    · rintro ⟨c₁, c₂, h₁, h₂, h₃⟩
      obtain ⟨c', h₄, h₅⟩ := ih.1 h₃
      exact ⟨c', ⟨c₁, c₂, h₁, h₂, h₄⟩, h₅⟩
    · rintro ⟨c', ⟨c₁, c₂, h₁, h₂, h₄⟩, h₅⟩
      exact ⟨c₁, c₂, h₁, h₂, ih.2 ⟨c', h₄, h₅⟩⟩

end Runs

/-! ## Silent runs against the universal host -/

section Silent

variable {I : ScalarInstance} {P : Profile}

/-- Against `instHost I`, a silent step is a host-free step: the host never diverges. -/
theorem hevNone_iff {c c' : Config Nat} :
    HEvStep P (instHost I) c none c' ↔ Step P (fun _ _ _ _ => False) c c' := by
  constructor
  · rintro (h | ⟨-, _, _, _, _, -, _, -, _, h⟩)
    · exact h
    · cases h
  · exact Or.inl

/-- A silent run against `instHost I` is a host-free Core run. -/
theorem silent_steps {c c' : Config Nat}
    (h : Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) c c') :
    Steps P (fun _ _ _ _ => False) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (hevNone_iff.1 h)

/-- A host-free machine run is a silent labelled run, for every host. -/
theorem reach_silent {host : HostSemantics Nat} {x y : Store Nat × Thread} (h : Reach P x y) :
    Relation.ReflTransGen (fun a b => HEvStep P host a none b) (x.2.config x.1)
      (y.2.config y.1) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hi ih =>
    obtain ⟨f', code', ht, hs⟩ := hi
    refine .tail ih ?_
    obtain ⟨s₂, t₂⟩ := c
    change t₂ = _ at ht
    subst ht
    exact Or.inl hs

/-- **A silent run against `instHost I` from a thread configuration is a host-free machine run.** -/
theorem silent_reach {c c' : Config Nat}
    (h : Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) c c')
    {s : Store Nat} {t : Thread} (hc : t.config s = c) :
    ∃ t', Reach P (s, t) (c'.store, t') ∧ t'.config c'.store = c' := by
  induction h with
  | refl =>
    subst hc
    refine ⟨t, ?_, ?_⟩ <;> rw [Thread.config_store]
  | @tail b c₂ _ hs ih =>
    obtain ⟨t', hr, ht'⟩ := ih
    refine ⟨.active c₂.frame c₂.code, hr.tail ⟨c₂.frame, c₂.code, rfl, ?_⟩, rfl⟩
    rw [ht']
    exact hevNone_iff.1 hs

end Silent

/-! ## Paths of the instance -/

section Paths

variable {I : ScalarInstance} {P : Profile}

theorem path_nil_iff {q q' : I.HState} : I.Path P q [] q' ↔ q = q' := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

theorem path_cons_iff {q q'' : I.HState} {m : Move I.E I.F} {p : List (Move I.E I.F)} :
    I.Path P q (m :: p) q'' ↔ ∃ q', I.Trans P q m q' ∧ I.Path P q' p q'' := by
  constructor
  · intro h; cases h with | cons h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨q', h₁, h₂⟩; exact .cons h₁ h₂

theorem path_single_iff {q q' : I.HState} {m : Move I.E I.F} :
    I.Path P q [m] q' ↔ I.Trans P q m q' := by
  rw [path_cons_iff]
  constructor
  · rintro ⟨_, h, h'⟩; rw [path_nil_iff] at h'; exact h' ▸ h
  · intro h; exact ⟨_, h, .nil _⟩

/-- From an idle store, an export question starts its pending invocation. -/
theorem path_idle_ask_iff {s : Store Nat} {a : I.F.Op} {p : List (Move I.E I.F)} {q : I.HState} :
    I.Path P (.idle s) (.inr (.ask a) :: p) q ↔ I.Path P (.running a s (I.initThread a)) p q := by
  rw [path_cons_iff]
  constructor
  · rintro ⟨_, h, h'⟩; cases h; exact h'
  · intro h; exact ⟨_, .call s a, h⟩

theorem callMoves_cons {E F : Sig.{0}} (x : Call E) (c : List (Call E)) :
    (callMoves (x :: c) : List (Move E F)) =
      .inl (.ask x.1) :: .inl (.ans x.1 x.2) :: callMoves c :=
  rfl

/-- **One import call of the instance is a silent run to the callout, then the event it views.** -/
theorem seg_fwd {a : I.F.Op} {s : Store Nat} {t : Thread} {x : Call I.E} {y q : I.HState}
    (h₁ : I.Trans P (.running a s t) (.inl (.ask x.1)) y)
    (h₂ : I.Trans P y (.inl (.ans x.1 x.2)) q) :
    ∃ ev c₁, CallView I x ev ∧
      Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) (t.config s) c₁ ∧
      ∃ s₂ t₂, q = .running a s₂ t₂ ∧ HEvStep P (instHost I) c₁ (some ev) (t₂.config s₂) := by
  obtain ⟨e, v⟩ := x
  cases h₁ with
  | ucall run callout op =>
    rename_i s' t' hh args
    cases h₂
    obtain ⟨E, a', hd⟩ := callout
    refine ⟨⟨(hh, s', args), (s', Answer.toResult v)⟩, t'.config s', ⟨op, rfl, rfl⟩,
      reach_silent run, _, _, rfl, E, a', ?_, ?_, ⟨e, op, v, ?_⟩, ?_⟩
    · rw [Thread.config_store]; exact hd
    · rw [Thread.config_store]
    · rw [Thread.config_store]
    · rw [resumeResult_config hd]

/-- **A silent run to a callout, then an event viewing an import call, is one import call of the
instance**, resuming in the configuration after the event. -/
theorem seg_bwd {a : I.F.Op} {s : Store Nat} {t : Thread} {x : Call I.E}
    {ev : Call (wasmHostSig Nat)} {c₁ c₂ : Config Nat} (hv : CallView I x ev)
    (h₁ : Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) (t.config s) c₁)
    (h₂ : HEvStep P (instHost I) c₁ (some ev) c₂) :
    ∃ y, I.Trans P (.running a s t) (.inl (.ask x.1)) y ∧
      I.Trans P y (.inl (.ans x.1 x.2)) (.running a c₂.store (.active c₂.frame c₂.code)) := by
  obtain ⟨e, v⟩ := x
  obtain ⟨⟨hh, s₀, us⟩, ⟨s₁, r⟩⟩ := ev
  obtain ⟨hop, hs₁, hr⟩ := hv
  simp only at hop hs₁ hr
  subst hs₁ hr
  obtain ⟨t', hreach, ht'⟩ := silent_reach h₁ rfl
  obtain ⟨E, a', hd, hst, -, rfl⟩ := h₂
  simp only at hd hst
  subst hst
  have hd' : decompose? c₁.store (t'.config c₁.store).code = some (E, a', hh, us) := by
    rw [ht']; exact hd
  have hres : resumeResult c₁.store t' (Answer.toResult v) =
      .active c₁.frame (E.fill (Answer.toResult v).toAdmin) := by
    unfold resumeResult
    simp only [hd']
    rw [ht']
  refine ⟨_, .ucall hreach ⟨E, a', hd'⟩ hop, ?_⟩
  have := ScalarInstance.Trans.uret (I := I) (P := P) (f := a) (s := c₁.store) (t := t') (e := e) v
  rw [hres] at this
  exact this

theorem path_append {q q' q'' : I.HState} {p p' : List (Move I.E I.F)} (h : I.Path P q p q')
    (h' : I.Path P q' p' q'') : I.Path P q (p ++ p') q'' := by
  induction h with
  | nil => exact h'
  | cons ht _ ih => exact .cons ht (ih h')

/-- **Instance runs along an import log are event-ended Core runs viewing it** (instance to
Core). -/
theorem path_calls_fwd {a : I.F.Op} {rest : List (Move I.E I.F)} {q : I.HState} :
    ∀ {c : List (Call I.E)} {s : Store Nat} {t : Thread},
      I.Path P (.running a s t) (callMoves c ++ rest) q →
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ s' t',
        EvRunE P (instHost I) (t.config s) cs (t'.config s') ∧ I.Path P (.running a s' t') rest q
  | [], s, t, h => ⟨[], .nil, s, t, rfl, h⟩
  | x :: c, s, t, h => by
    rw [callMoves_cons, List.cons_append, List.cons_append] at h
    obtain ⟨y, h₁, h'⟩ := path_cons_iff.1 h
    obtain ⟨q', h₂, h''⟩ := path_cons_iff.1 h'
    obtain ⟨ev, c₁, hv, hsil, s₂, t₂, rfl, hev⟩ := seg_fwd h₁ h₂
    obtain ⟨cs, hF, s', t', hE, hp⟩ := path_calls_fwd h''
    exact ⟨ev :: cs, .cons hv hF, s', t', ⟨c₁, t₂.config s₂, hsil, hev, hE⟩, hp⟩

/-- **Event-ended Core runs viewing an import log are instance runs along it** (Core to
instance). -/
theorem path_calls_bwd {a : I.F.Op} :
    ∀ {c : List (Call I.E)} {cs : List (Call (wasmHostSig Nat))} {s : Store Nat} {t : Thread}
      {c' : Config Nat}, List.Forall₂ (CallView I) c cs → EvRunE P (instHost I) (t.config s) cs c' →
      ∃ s' t', t'.config s' = c' ∧ I.Path P (.running a s t) (callMoves c) (.running a s' t')
  | [], [], s, t, _, .nil, hE => ⟨s, t, hE.symm, .nil _⟩
  | _ :: _, _ :: _, _, _, _, .cons hv hF, hE => by
    obtain ⟨c₁, c₂, hsil, hev, hE'⟩ := hE
    obtain ⟨y, h₁, h₂⟩ := seg_bwd (a := a) hv hsil hev
    obtain ⟨s', t', hc, hp⟩ := path_calls_bwd (a := a) (s := c₂.store)
      (t := .active c₂.frame c₂.code) hF hE'
    exact ⟨s', t', hc, .cons h₁ (.cons h₂ hp)⟩

end Paths

/-! ## Activations -/

section Activations

variable {I : ScalarInstance} {P : Profile}

theorem config_mk {H : Type} {cfg : Config H} {s : Store H} {f : Frame} {code : List Admin}
    (h₁ : cfg.store = s) (h₂ : cfg.frame = f) (h₃ : cfg.code = code) : cfg = ⟨s, f, code⟩ := by
  cases cfg; cases h₁; cases h₂; cases h₃; rfl

/-- **A returning activation is a labelled Core run in the empty frame to a result it reads.** -/
theorem ret_iff {s s' : Store Nat} {a : I.F.Op} {v : I.F.Ar a} {c : List (Call I.E)} :
    I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inr (.ans a v)])) (.idle s') ↔
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ r, Answer.ofResult? (I.exports.get a.1) r = some v ∧
        EvRun P (instHost I) (invoke s (qOf I a).1 (qOf I a).2) cs ⟨s', {}, r.toAdmin⟩ := by
  rw [path_idle_ask_iff]
  constructor
  · intro h
    obtain ⟨cs, hF, s₁, t₁, hE, hp⟩ := path_calls_fwd h
    rw [path_single_iff] at hp
    cases hp with
    | oret run final answer =>
      rename_i t₃ r
      have hrun : EvRun P (instHost I) (invoke s (qOf I a).1 (qOf I a).2) cs (t₃.config s') :=
        evRun_iff.2 ⟨_, hE, reach_silent run⟩
      have h₃ : t₃.config s' = ⟨s', {}, r.toAdmin⟩ :=
        config_mk (Thread.config_store s' t₃) (evRun_invoke_frame hrun) final
      exact ⟨cs, hF, r, answer, h₃ ▸ hrun⟩
  · rintro ⟨cs, hF, r, hr, hrun⟩
    obtain ⟨c', hE, hsil⟩ := evRun_iff.1 hrun
    obtain ⟨s₁, t₁, hc, hp⟩ := path_calls_bwd (a := a) (s := s) (t := I.initThread a) hF hE
    obtain ⟨t₃, hreach, h₃⟩ := silent_reach hsil hc
    have final : ResultAt s' t₃ r := by
      show (t₃.config s').code = r.toAdmin
      rw [h₃]
    exact path_append hp (path_single_iff.2 (.oret hreach final hr))

theorem diverges_iff {x : Store Nat × Thread} :
    InstStrat.Diverges P x ↔ InfiniteTrace (InternalP P) x := Iff.rfl

/-- Host-free machine divergence is host-free Core divergence of the thread configuration. -/
theorem diverges_config {x : Store Nat × Thread} (h : InstStrat.Diverges P x) :
    Diverges P (fun _ _ _ _ => False) (x.2.config x.1) := by
  rw [diverges_iff] at h
  refine InfiniteTrace.map (fun x : Store Nat × Thread => x.2.config x.1) ?_ h
  rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ ⟨f', code', ht, hs⟩
  change t₂ = _ at ht
  subst ht
  exact hs

/-- Host-free Core divergence of a thread configuration is host-free machine divergence. -/
theorem diverges_of_config {x : Store Nat × Thread}
    (h : Diverges P (fun _ _ _ _ => False) (x.2.config x.1)) : InstStrat.Diverges P x := by
  rw [diverges_iff]
  refine InfiniteTrace.of_map (fun x : Store Nat × Thread => x.2.config x.1) (fun _ => True)
    ?_ trivial h
  intro y b _ hs
  exact ⟨(b.store, .active b.frame b.code), ⟨b.frame, b.code, rfl, hs⟩, trivial, rfl⟩

/-- **A divergent activation is a labelled Core run followed by host-free divergence.** -/
theorem div_iff {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    (∃ s' t, I.Path P (.idle s) (.inr (.ask a) :: callMoves c) (.running a s' t) ∧
        InstStrat.Diverges P (s', t)) ↔
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ c', EvRun P (instHost I)
        (invoke s (qOf I a).1 (qOf I a).2) cs c' ∧ Diverges P (fun _ _ _ _ => False) c' := by
  constructor
  · rintro ⟨s', t', hp, hd⟩
    rw [path_idle_ask_iff, ← List.append_nil (callMoves c)] at hp
    obtain ⟨cs, hF, s₁, t₁, hE, hp'⟩ := path_calls_fwd hp
    rw [path_nil_iff] at hp'
    cases hp'
    exact ⟨cs, hF, _, evRun_iff.2 ⟨_, hE, .refl⟩, diverges_config hd⟩
  · rintro ⟨cs, hF, c'', hrun, hdiv⟩
    obtain ⟨c', hE, hsil⟩ := evRun_iff.1 hrun
    obtain ⟨s₁, t₁, hc, hp⟩ := path_calls_bwd (a := a) (s := s) (t := I.initThread a) hF hE
    have hd : Diverges P (fun _ _ _ _ => False) c' :=
      InfiniteTrace.of_steps (silent_steps hsil) hdiv
    refine ⟨s₁, t₁, path_idle_ask_iff.2 hp, diverges_of_config ?_⟩
    exact hc ▸ hd

/-- **A pending import call is a reached Core callout viewing it.** -/
theorem pend_iff {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} {e : I.E.Op} :
    (∃ q, I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inl (.ask e)])) q) ↔
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ m : (wasmHostSig Nat).Op,
        I.importOp? m.1 m.2.2 = some e ∧ CoreCallout P (instHost I) s (qOf I a) (cs, m) := by
  constructor
  · rintro ⟨q, hp⟩
    rw [path_idle_ask_iff] at hp
    obtain ⟨cs, hF, s₁, t₁, hE, hp'⟩ := path_calls_fwd hp
    rw [path_single_iff] at hp'
    cases hp' with
    | ucall run callout op =>
      rename_i s' t' hh args
      obtain ⟨E, a', hd⟩ := callout
      refine ⟨cs, hF, (hh, s', args), op, t'.config s', E, a',
        evRun_iff.2 ⟨_, hE, reach_silent run⟩, ?_, Thread.config_store s' t'⟩
      rw [Thread.config_store]; exact hd
  · rintro ⟨cs, hF, ⟨hh, s₂, us⟩, hop, c'', E, a', hrun, hd, -⟩
    obtain ⟨c', hE, hsil⟩ := evRun_iff.1 hrun
    obtain ⟨s₁, t₁, hc, hp⟩ := path_calls_bwd (a := a) (s := s) (t := I.initThread a) hF hE
    obtain ⟨t₃, hreach, h₃⟩ := silent_reach hsil hc
    have callout : CalloutAt c''.store t₃ hh us := ⟨E, a', by rw [h₃]; exact hd⟩
    exact ⟨_, path_idle_ask_iff.2 (path_append hp (path_single_iff.2 (.ucall hreach callout hop)))⟩

/-- The Core configuration of a hidden state (the thread's, when there is one). -/
def hcfg : I.HState → Config Nat
  | .idle s => ⟨s, {}, []⟩
  | .running _ s t => t.config s
  | .waiting _ s t _ => t.config s

/-- The hidden states of a productive Core run. -/
def infState (a : I.F.Op) (s : Store Nat) (g : ℕ → Config Nat) : ℕ → I.HState
  | 0 => .running a s (I.initThread a)
  | k + 1 => .running a (g (k + 1)).store (.active (g (k + 1)).frame (g (k + 1)).code)

/-- **A productive run of the instance is a productive Core run viewing its stream.** -/
theorem inf_iff {s : Store Nat} {a : I.F.Op} {ω : ℕ → Call I.E} :
    ω ∈ InstStrat.instInf I P s a ↔ ∃ ω', CoreInf P (instHost I)
      (invoke s (qOf I a).1 (qOf I a).2) ω' ∧ ∀ k, CallView I (ω k) (ω' k) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hrun : ∀ k, ∃ s' t', x k = .running a s' t' := by
      intro k
      induction k with
      | zero => exact ⟨_, _, hx0⟩
      | succ k ih =>
        obtain ⟨s', t', hk⟩ := ih
        obtain ⟨y, h₁, h₂⟩ := hx k
        rw [hk] at h₁
        obtain ⟨_, _, _, _, s₂, t₂, hq, _⟩ := seg_fwd h₁ h₂
        exact ⟨s₂, t₂, hq⟩
    have hseg : ∀ k, ∃ ev c₁, CallView I (ω k) ev ∧
        Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) (hcfg (x k)) c₁ ∧
        HEvStep P (instHost I) c₁ (some ev) (hcfg (x (k + 1))) := by
      intro k
      obtain ⟨s', t', hk⟩ := hrun k
      obtain ⟨y, h₁, h₂⟩ := hx k
      rw [hk] at h₁
      obtain ⟨ev, c₁, hv, hsil, s₂, t₂, hq, hev⟩ := seg_fwd h₁ h₂
      refine ⟨ev, c₁, hv, ?_, ?_⟩
      · rw [hk]; exact hsil
      · rw [hq]; exact hev
    choose ev c₁ hv hsil hev using hseg
    refine ⟨ev, ⟨fun k => hcfg (x k), ?_, fun n => ⟨c₁ n, hsil n, hev n⟩⟩, hv⟩
    show hcfg (x 0) = _
    rw [hx0]
    rfl
  · rintro ⟨ω', ⟨g, hg0, hg⟩, hv⟩
    have hcfgx : ∀ k, ∃ s' t', infState a s g k = .running a s' t' ∧ t'.config s' = g k := by
      intro k
      cases k with
      | zero => exact ⟨s, I.initThread a, rfl, hg0.symm⟩
      | succ k => exact ⟨_, _, rfl, rfl⟩
    refine ⟨infState a s g, rfl, fun k => ?_⟩
    obtain ⟨s', t', hk, hc⟩ := hcfgx k
    obtain ⟨c₁, hs₁, he₁⟩ := hg k
    rw [hk]
    rw [← hc] at hs₁
    obtain ⟨y, h₁, h₂⟩ := seg_bwd (a := a) (hv k) hs₁ he₁
    exact ⟨y, h₁, h₂⟩

end Activations

/-! ## The triples -/

section Triples

variable {I : ScalarInstance} {P : Profile}

theorem resOf_cAns (r : Result) : resOf (cAns r) = r := by cases r <;> rfl

theorem coreBeh_ret {s : Store Nat} {q : Nat × List Val} {cs : List (Call (wasmHostSig Nat))}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}} {s₂ : Store Nat} :
    CoreBehSXP P (instHost I) s q (cs, .ret b s₂) ↔
      EvRun P (instHost I) (invoke s q.1 q.2) cs ⟨s₂, {}, (resOf b).toAdmin⟩ := by
  rcases b with (ws | t) | u <;> exact Iff.rfl

theorem mem_fin {s : Store Nat} {a : I.F.Op}
    {x : CallBeh I.E (Store Nat) (InstSession.Res I.exports ⊕ PUnit.{1})} :
    x ∈ (InstSession.instTripleS I P).1 s a ↔
      x ∈ (viewTriple I (coreTripleSO P (instHost I))).1 s a := by
  obtain ⟨c, e'⟩ := x
  change ((∃ (v : I.F.Ar a) (s' : Store Nat), e' = .ret (InstSession.sAns a v) s' ∧
      I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inr (.ans a v)])) (.idle s')) ∨
    (e' = .div ∧ ∃ s' t, I.Path P (.idle s) (.inr (.ask a) :: callMoves c) (.running a s' t) ∧
      InstStrat.Diverges P (s', t))) ↔
    ∃ y, (True ∧ CoreBehSXP P (instHost I) s (qOf I a) y) ∧
      List.Forall₂ (CallView I) c y.1 ∧ viewEnd I a y.2 = some e'
  constructor
  · rintro (⟨v, s', rfl, hp⟩ | ⟨rfl, hd⟩)
    · obtain ⟨cs, hF, r, hr, hrun⟩ := ret_iff.1 hp
      refine ⟨(cs, .ret (cAns r) s'), ⟨trivial, coreBeh_ret.2 ?_⟩, hF, ?_⟩
      · rw [resOf_cAns]; exact hrun
      · simp only [viewEnd, resOf_cAns, hr, Option.map_some]
    · obtain ⟨cs, hF, c', hrun, hdiv⟩ := div_iff.1 hd
      exact ⟨(cs, .div), ⟨trivial, c', hrun, hdiv⟩, hF, rfl⟩
  · rintro ⟨⟨cs, ey⟩, ⟨-, hb⟩, hF, hv⟩
    cases ey with
    | ret b s₂ =>
      simp only [viewEnd, Option.map_eq_some_iff] at hv
      obtain ⟨v, hv, rfl⟩ := hv
      exact .inl ⟨v, s₂, rfl, ret_iff.2 ⟨cs, hF, resOf b, hv, coreBeh_ret.1 hb⟩⟩
    | trap => exact (show False from hb).elim
    | div =>
      cases hv
      exact .inr ⟨rfl, div_iff.2 ⟨cs, hF, hb⟩⟩

theorem mem_pend {s : Store Nat} {a : I.F.Op} {x : List (Call I.E) × I.E.Op} :
    x ∈ (InstSession.instTripleS I P).2.1 s a ↔
      x ∈ (viewTriple I (coreTripleSO P (instHost I))).2.1 s a := by
  obtain ⟨c, e⟩ := x
  change (∃ q, I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inl (.ask e)])) q) ↔
    ∃ y, CoreCallout P (instHost I) s (qOf I a) y ∧
      List.Forall₂ (CallView I) c y.1 ∧ I.importOp? y.2.1 y.2.2.2 = some e
  rw [pend_iff]
  constructor
  · rintro ⟨cs, hF, m, hm, hc⟩
    exact ⟨(cs, m), hc, hF, hm⟩
  · rintro ⟨⟨cs, m⟩, hc, hF, hm⟩
    exact ⟨cs, hF, m, hm, hc⟩

theorem mem_inf {s : Store Nat} {a : I.F.Op} {ω : ℕ → Call I.E} :
    ω ∈ (InstSession.instTripleS I P).2.2 s a ↔
      ω ∈ (viewTriple I (coreTripleSO P (instHost I))).2.2 s a := by
  change ω ∈ InstStrat.instInf I P s a ↔
    ∃ ω', (True ∧ CoreInf P (instHost I) (invoke s (qOf I a).1 (qOf I a).2) ω') ∧
      ∀ k, CallView I (ω k) (ω' k)
  rw [inf_iff]
  constructor
  · rintro ⟨ω', h, hv⟩; exact ⟨ω', ⟨trivial, h⟩, hv⟩
  · rintro ⟨ω', ⟨-, h⟩, hv⟩; exact ⟨ω', h, hv⟩

/-- **The open instance triple is the view of the open Core triple at the universal
store-preserving host.** -/
theorem instTripleS_eq_viewTriple :
    InstSession.instTripleS I P = viewTriple I (coreTripleSO P (instHost I)) :=
  Prod.ext (funext fun _ => funext fun _ => Set.ext fun _ => mem_fin)
    (Prod.ext (funext fun _ => funext fun _ => Set.ext fun _ => mem_pend)
      (funext fun _ => funext fun _ => Set.ext fun _ => mem_inf))

/-- At the universal host, no blocked or host-divergent callout of `coreTripleSXP` has a view. -/
theorem not_mem_view_pend_coreTripleSXP (s : Store Nat) (a : I.F.Op)
    (x : List (Call I.E) × I.E.Op) :
    x ∉ (viewTriple I (coreTripleSXP P (instHost I) fun _ _ => True)).2.1 s a := by
  rintro ⟨⟨cs, hh, s', us⟩, ⟨-, hb | hb⟩, -, hop⟩
  · obtain ⟨_, _, _, -, -, -, hno⟩ := hb
    exact hno _ ⟨x.2, hop, .trap, rfl⟩
  · obtain ⟨_, _, _, -, -, -, ⟨_, -, _, h⟩⟩ := hb
    cases h

end Triples

end Silmaril.Proofs.Wasm.Abstract.NodeBridge
