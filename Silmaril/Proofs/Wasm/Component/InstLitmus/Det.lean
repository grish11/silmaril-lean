module

public import Silmaril.Proofs.Wasm.Component.InstLitmus.Pos
public import Silmaril.Proofs.Wasm.Component.InstSem.Script
public import Silmaril.Proofs.Wasm.Component.Core3G.Lawful
public import Silmaril.Wasm.Game.Machine.Thms

/-!
# Instantiation litmus modules at a deterministic profile: scripts

At a deterministic profile `profile o`, host-free Core 3.0 runs reach at most one normal form
(`Silmaril.Wasm.Game.reach_normal_unique`). So the start function of `callMod k` can only call
`f(k)` and then return or trap according to the answer, and that of `trapMod` can only trap.
Each module is therefore bounded by a *script* (a handler): `callMod_le_script`,
`trapMod_le_script`, by simulations of the engine's transition system in the handler's.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game (statusP Reach)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

/-! ## Normal forms -/

variable {o : GrowOracle}

theorem noStep_callout {P : Profile} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {h : Nat} {args : List Flat} (hs : (core3P P).status s t = .callout h args) :
    ∀ y, ¬ Silmaril.Wasm.Game.InternalP P (s, t) y := by
  obtain ⟨h', args', hst⟩ := Silmaril.Proofs.Wasm.Component.Core3G.flatStatus_eq_callout hs
  exact Silmaril.Proofs.Wasm.Component.Core3G.statusP_callout_no_step hst

theorem noStep_returned {P : Profile} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {r : Silmaril.Wasm.Component.Engine.CallResult} (hs : (core3P P).status s t = .returned r) :
    ∀ y, ¬ Silmaril.Wasm.Game.InternalP P (s, t) y := by
  rcases Silmaril.Proofs.Wasm.Component.Core3G.flatStatus_eq_returned hs with ⟨vs, hst⟩ | hst
  · exact Silmaril.Proofs.Wasm.Component.Core3G.statusP_returned_no_step hst
  · exact Silmaril.Proofs.Wasm.Component.Core3G.statusP_returned_no_step hst

/-- A normal form: a callout or a returned status. -/
def Normal (P : Profile) (c : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) : Prop :=
  (∃ h args, (core3P P).status c.1 c.2 = .callout h args) ∨
    ∃ r, (core3P P).status c.1 c.2 = .returned r

theorem noStep_normal {P : Profile} {c : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
    (h : Normal P c) : ∀ y, ¬ Silmaril.Wasm.Game.InternalP P c y := by
  rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
  · exact noStep_callout h
  · exact noStep_returned h

/-- **Runs to normal forms are unique**, at a deterministic profile. -/
theorem normal_unique {x y y' : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
    (h : ESteps (core3P (profile o)) x y) (h' : ESteps (core3P (profile o)) x y')
    (hy : Normal (profile o) y) (hy' : Normal (profile o) y') : y = y' :=
  Silmaril.Wasm.Game.reach_normal_unique h h' (noStep_normal hy) (noStep_normal hy')

/-! ## Scripts -/

/-- The instantiation answer of a start function resumed with the host's answer `r` to an import
call with no results: `ready` for `()`, `fail` for anything else (a trap). -/
def okA (r : Option Payload) : InstAns Unit :=
  match resultOf [] r with
  | .values _ => .ready
  | .trap => .fail ()

theorem resultOf_nil (r : Option Payload) :
    (resultOf [] r = .values [] ∧ okA r = .ready) ∨ (resultOf [] r = .trap ∧ okA r = .fail ()) := by
  unfold okA
  rcases r with _ | (ys | vs)
  · exact .inr ⟨rfl, rfl⟩
  · by_cases h : FlatTyped [] ys
    · have hy : ys = [] := List.map_eq_nil_iff.1 h
      subst hy
      left
      simp only [resultOf, h, ↓reduceIte, and_self]
    · right
      simp only [resultOf, h, ↓reduceIte, and_self]
  · exact .inr ⟨rfl, rfl⟩

/-- **The script of `callMod k`**: on `inst`, call `f(k)`; answer `ready` on `()`, `fail` on
anything else. It has no exports. -/
def callS (k : BitVec 32) : Handler (sigN 1) ((sigN 0).withInst Unit) := fun q =>
  match q with
  | none => .call (⟨0, Nat.zero_lt_one⟩, .flat [Flat.i32 k]) fun r => .pure (okA r)
  | some q => q.1.elim0

/-- **The script of `trapMod`**: on `inst`, fail. -/
def trapS : Handler (sigN 0) ((sigN 1).withInst Unit) := fun q =>
  match q with
  | none => .pure (.fail ())
  | some _ => .pure none

/-- The question `f(k)` at the module's interface. -/
abbrev fM₀ (k : BitVec 32) : (sigN (callMod k).imports.length).Op :=
  (⟨0, Nat.zero_lt_one⟩, .flat [Flat.i32 k])

/-- The relation of the simulation of `callMod k` by its script. -/
inductive CallRel (P : Profile) (k : BitVec 32) (s₀ : Store Nat)
    (t₁ : Silmaril.Wasm.SingleThreaded.Thread) :
    IState (core3P P) (callMod k).imports.length (callMod k).exports.length →
      (callS k).toReduction.State → Prop
  | fresh : CallRel P k s₀ t₁ .fresh .idle
  | pre {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
      (h : ESteps (core3P P) (s₀, (core3P P).invoke (1 : Nat) []) (s, t)) :
      CallRel P k s₀ t₁ (.starting s t) (.run none (callS k none))
  | wait : CallRel P k s₀ t₁ (.startWait s₀ t₁ (fM₀ k)) (.wait none (fM₀ k) fun r => .pure (okA r))
  | post {r : Option Payload} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
      (h : ESteps (core3P P) (s₀, (core3P P).resume s₀ t₁ (resultOf [] r)) (s, t)) :
      CallRel P k s₀ t₁ (.starting s t) (.run none (.pure (okA r)))
  | readying {s : Store Nat} : CallRel P k s₀ t₁ (.readying s) (.run none (.pure .ready))
  | failing : CallRel P k s₀ t₁ .failing (.run none (.pure (.fail ())))
  | ready {x : EState (core3P P) (callMod k).imports.length (callMod k).exports.length} :
      CallRel P k s₀ t₁ (.ready x) .idle
  | dead : CallRel P k s₀ t₁ .dead .idle

theorem no_etrans_nil {E : Engine} {addrs : List E.FuncAddr} {imps exps : CoreIface}
    {x y : EState E imps.length exps.length} {m : Move (sigN imps.length) (sigN exps.length)}
    (h : ETrans E addrs imps exps x m y) (he : exps = []) : False := by
  subst he
  cases h with
  | @call _ q _ _ _ => exact q.1.elim0
  | @refuse _ q _ => exact q.1.elim0
  | @refused _ q => exact q.1.elim0
  | @ucall q _ _ _ _ _ _ _ _ _ => exact q.1.elim0
  | @uret q _ _ _ _ => exact q.1.elim0
  | @oret q _ _ _ _ _ _ _ => exact q.1.elim0
  | @otrap q _ _ _ _ _ _ => exact q.1.elim0

/-- **`callMod k` is bounded by its script**, at a deterministic profile. -/
theorem callMod_le_script {k : BitVec 32} (hk : prepOk 1 (callStoreOk k) (callPrep k) = true) :
    (core3SemI (profile o)).sem (callMod k) ≤ Strategy.ofHandler (callS k) := by
  show engineStrategyI (core3P (profile o)) (instOfI (core3P (profile o)) (callMod k).mod
    (callMod k).imports (callMod k).exports) (callMod k).imports (callMod k).exports ≤ _
  rw [instOfI_call _ hk]
  obtain ⟨_, -, hs⟩ := prepOk_eq hk
  obtain ⟨t₁, hr₁, hco, ⟨tv, hrv, hfv⟩, ⟨tt, hrt, hft⟩⟩ := call_start (P := profile o) hs
  have hn₁ : Normal (profile o) (storeOf (callPrep k), t₁) := .inl ⟨_, _, hco⟩
  -- the start phase after the answer `r` ends at `tv` or `tt`
  have hpost : ∀ r, ∃ t', ESteps (core3P (profile o)) (storeOf (callPrep k),
      (core3P (profile o)).resume (storeOf (callPrep k)) t₁ (resultOf [] r))
      (storeOf (callPrep k), t') ∧
      (core3P (profile o)).status (storeOf (callPrep k)) t' =
        .returned (match resultOf [] r with | .values _ => .values [] | .trap => .trap) ∧
      ((okA r = .ready ∧ resultOf [] r = .values []) ∨ (okA r = .fail () ∧ resultOf [] r = .trap)) := by
    intro r
    rcases resultOf_nil r with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨tv, by rw [h1]; exact hrv, by rw [h1]; exact hfv, .inl ⟨h2, h1⟩⟩
    · exact ⟨tt, by rw [h1]; exact hrt, by rw [h1]; exact hft, .inr ⟨h2, h1⟩⟩
  refine LTS.Simulation.ofLTS_le ⟨CallRel (profile o) k (storeOf (callPrep k)) t₁, .fresh, ?_⟩
  intro x x' y l hR hstep
  change ITrans (core3P (profile o)) (some (callI (profile o) k)) (callMod k).imports
    (callMod k).exports x l x' at hstep
  cases hR with
  | fresh =>
    cases hstep with
    | start hI ha =>
      cases hI
      cases ha
      exact ⟨_, .vis (Reduction.Step.ask (R := (callS k).toReduction) (none : Option (sigN 0).Op))
        (.nil _), .pre .refl⟩
    | noStart hI ha => cases hI; cases ha
    | noInst hI => cases hI
  | pre h =>
    cases hstep with
    | scall run callout hh =>
      have heq := normal_unique (h.trans run) hr₁ (.inl ⟨_, _, callout⟩) hn₁
      cases heq
      rw [hco] at callout
      cases callout
      exact ⟨_, .vis (.call rfl) (.nil _), .wait⟩
    | sdone run final =>
      exact absurd (normal_unique (h.trans run) hr₁ (.inr ⟨_, final⟩) hn₁) fun heq => by
        cases heq; rw [hco] at final; cases final
    | strap run final =>
      exact absurd (normal_unique (h.trans run) hr₁ (.inr ⟨_, final⟩) hn₁) fun heq => by
        cases heq; rw [hco] at final; cases final
  | wait =>
    cases hstep with
    | sret r => exact ⟨_, .vis (Reduction.Step.resume (R := (callS k).toReduction) none (fM₀ k)
      (fun r => .pure (okA r)) (r : Option Payload)) (.nil _), .post .refl⟩
  | post h =>
    rename_i r _ _
    obtain ⟨t', hr', hf', hok⟩ := hpost r
    cases hstep with
    | scall run callout hh =>
      exact absurd (normal_unique (h.trans run) hr' (.inl ⟨_, _, callout⟩) (.inr ⟨_, hf'⟩))
        fun heq => by cases heq; rw [hf'] at callout; cases callout
    | sdone run final =>
      have heq := normal_unique (h.trans run) hr' (.inr ⟨_, final⟩) (.inr ⟨_, hf'⟩)
      cases heq
      rcases hok with ⟨hok, -⟩ | ⟨-, hres⟩
      · rw [hok]; exact ⟨_, .nil _, .readying⟩
      · rw [hf', hres] at final; cases final
    | strap run final =>
      have heq := normal_unique (h.trans run) hr' (.inr ⟨_, final⟩) (.inr ⟨_, hf'⟩)
      cases heq
      rcases hok with ⟨-, hres⟩ | ⟨hok, -⟩
      · rw [hf', hres] at final; cases final
      · rw [hok]; exact ⟨_, .nil _, .failing⟩
  | readying =>
    cases hstep with
    | ready => exact ⟨_, .vis (.ret rfl) (.nil _), .ready⟩
  | failing =>
    cases hstep with
    | fail => exact ⟨_, .vis (.ret rfl) (.nil _), .dead⟩
  | ready =>
    cases hstep with
    | lift h => exact (no_etrans_nil h rfl).elim
  | dead => cases hstep

/-- The relation of the simulation of `trapMod` by its script. -/
inductive TrapRel (P : Profile) (s₀ : Store Nat) :
    IState (core3P P) trapMod.imports.length trapMod.exports.length →
      trapS.toReduction.State → Prop
  | fresh : TrapRel P s₀ .fresh .idle
  | pre {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
      (h : ESteps (core3P P) (s₀, (core3P P).invoke (0 : Nat) []) (s, t)) :
      TrapRel P s₀ (.starting s t) (.run none (.pure (.fail ())))
  | failing : TrapRel P s₀ .failing (.run none (.pure (.fail ())))
  | dead : TrapRel P s₀ .dead .idle

/-- **`trapMod` is bounded by its script**, at a deterministic profile. -/
theorem trapMod_le_script :
    (core3SemI (profile o)).sem trapMod ≤ Strategy.ofHandler trapS := by
  show engineStrategyI (core3P (profile o)) (instOfI (core3P (profile o)) trapMod.mod
    trapMod.imports trapMod.exports) trapMod.imports trapMod.exports ≤ _
  rw [instOfI_trap]
  obtain ⟨_, -, hs⟩ := prepOk_eq trapPrep_ok.1
  obtain ⟨t₁, hr₁, hf₁⟩ := trap_start (P := profile o) hs
  have hn₁ : Normal (profile o) (storeOf trapPrep, t₁) := .inr ⟨_, hf₁⟩
  refine LTS.Simulation.ofLTS_le ⟨TrapRel (profile o) (storeOf trapPrep), .fresh, ?_⟩
  intro x x' y l hR hstep
  change ITrans (core3P (profile o)) (some (trapI (profile o))) trapMod.imports
    trapMod.exports x l x' at hstep
  cases hR with
  | fresh =>
    cases hstep with
    | start hI ha =>
      cases hI
      cases ha
      exact ⟨_, .vis (Reduction.Step.ask (R := trapS.toReduction) (none : Option (sigN 1).Op))
        (.nil _), .pre .refl⟩
    | noStart hI ha => cases hI; cases ha
    | noInst hI => cases hI
  | pre h =>
    cases hstep with
    | scall run callout hh =>
      exact absurd (normal_unique (h.trans run) hr₁ (.inl ⟨_, _, callout⟩) hn₁) fun heq => by
        cases heq; rw [hf₁] at callout; cases callout
    | sdone run final =>
      exact absurd (normal_unique (h.trans run) hr₁ (.inr ⟨_, final⟩) hn₁) fun heq => by
        cases heq; rw [hf₁] at final; cases final
    | strap run final => exact ⟨_, .nil _, .failing⟩
  | failing =>
    cases hstep with
    | fail => exact ⟨_, .vis (.ret rfl) (.nil _), .dead⟩
  | dead => cases hstep

end Silmaril.Proofs.Wasm.Component.InstLitmus
