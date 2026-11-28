module

public import Silmaril.Logic.Temporal.TLA.Defs
import Silmaril.Proofs.Logic.Temporal.TLA.Stuttering
import Silmaril.Proofs.Logic.Temporal.TLA.Temporal

public section

namespace Silmaril.Logic.Temporal.TLA

universe u v w

variable {S V W : Type u}

namespace Formula

theorem holds_suffix (p : Formula S) (σ : Behavior S) (n i : Nat) :
    p.Holds (σ.suffix n) i ↔ p.Holds σ (n + i) :=
  Proofs.Logic.Temporal.TLA.holds_suffix p σ n i

theorem sat_suffix (p : Formula S) (σ : Behavior S) (n : Nat) :
    p.Sat (σ.suffix n) ↔ p.Holds σ n := p.holds_suffix σ n 0

theorem holds_disj (p q : Formula S) (σ : Behavior S) (n : Nat) :
    (p.disj q).Holds σ n ↔ p.Holds σ n ∨ q.Holds σ n :=
  Proofs.Logic.Temporal.TLA.holds_disj p q σ n

theorem holds_imp (p q : Formula S) (σ : Behavior S) (n : Nat) :
    (p.imp q).Holds σ n ↔ (p.Holds σ n → q.Holds σ n) :=
  Proofs.Logic.Temporal.TLA.holds_imp p q σ n

theorem holds_existsRigid (p : V → Formula S) (σ : Behavior S) (n : Nat) :
    (Formula.existsRigid p).Holds σ n ↔ ∃ v, (p v).Holds σ n := Iff.rfl

theorem holds_existsFlex (p : Formula (S × V)) (σ : Behavior S) (n : Nat) :
    (Formula.existsFlex p).Holds σ n ↔ hide p.Sat (σ.suffix n) := Iff.rfl

theorem sat_existsFlex (p : Formula (S × V)) (σ : Behavior S) :
    (Formula.existsFlex p).Sat σ ↔ hide p.Sat σ := by
  have h : σ.suffix 0 = σ := funext fun i => congrArg σ (Nat.zero_add i)
  simpa only [h, Sat] using holds_existsFlex p σ 0

theorem sat_forallFlex (p : Formula (S × V)) (σ : Behavior S) :
    (p.forallFlex).Sat σ ↔ ∀ τ, StutterEquiv σ (τ.map Prod.fst) → p.Sat τ := by
  classical
  change ¬(Formula.existsFlex (.neg p)).Sat σ ↔ _
  rw [sat_existsFlex]
  simp only [hide, not_exists, not_and, Formula.Sat, Formula.Holds, Classical.not_not]

theorem holds_forallRigid (p : V → Formula S) (σ : Behavior S) (n : Nat) :
    (Formula.forallRigid p).Holds σ n ↔ ∀ v, (p v).Holds σ n := by
  classical
  simp only [Formula.forallRigid, Formula.Holds, not_exists, Classical.not_not]

theorem holds_eventually (p : Formula S) (σ : Behavior S) (n : Nat) :
    p.eventually.Holds σ n ↔ ∃ j, n ≤ j ∧ p.Holds σ j :=
  Proofs.Logic.Temporal.TLA.holds_eventually p σ n

theorem holds_eventuallyAngle (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (eventuallyAngle A f).Holds σ n ↔ ∃ j, n ≤ j ∧ A.angle f (σ j) (σ (j + 1)) :=
  Proofs.Logic.Temporal.TLA.holds_eventuallyAngle A f σ n

theorem holds_leadsTo (p q : Formula S) (σ : Behavior S) (n : Nat) :
    (p.leadsTo q).Holds σ n ↔
      ∀ i, n ≤ i → p.Holds σ i → ∃ j, i ≤ j ∧ q.Holds σ j :=
  Proofs.Logic.Temporal.TLA.holds_leadsTo p q σ n

/-- Continuous enablement from some point forces recurrent angle steps. -/
theorem holds_weakFair (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (weakFair A f).Holds σ n ↔
      ((∃ i, n ≤ i ∧ ∀ j, i ≤ j → (A.angle f).enabled (σ j)) →
        ∀ i, n ≤ i → ∃ j, i ≤ j ∧ A.angle f (σ j) (σ (j + 1))) :=
  Proofs.Logic.Temporal.TLA.holds_weakFair A f σ n

/-- Recurrent enablement forces recurrent angle steps. -/
theorem holds_strongFair (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (strongFair A f).Holds σ n ↔
      ((∀ i, n ≤ i → ∃ j, i ≤ j ∧ (A.angle f).enabled (σ j)) →
        ∀ i, n ≤ i → ∃ j, i ≤ j ∧ A.angle f (σ j) (σ (j + 1))) :=
  Proofs.Logic.Temporal.TLA.holds_strongFair A f σ n

theorem strongFair_implies_weakFair (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (strongFair A f).Holds σ n → (weakFair A f).Holds σ n :=
  Proofs.Logic.Temporal.TLA.strongFair_implies_weakFair A f σ n

/-- Induct on steps, including all steps preserving the observation `f`. -/
theorem spec_invariant {init p : StatePred S} {next : Action S} {f : StateExpr S V}
    (live : Formula S) (initial : ∀ s, init s → p s)
    (preserve : ∀ s t, p s → next.bracket f s t → p t) :
    (spec init next f live).Entails (.always (.state p)) :=
  Proofs.Logic.Temporal.TLA.spec_invariant live initial preserve

/-- A semantic weak-fairness progress rule. While waiting in `p`, allowed steps
maintain `p` or reach `q`, and the enabled fair angle action establishes `q`. -/
theorem weakFair_progress {p q : StatePred S} {next A : Action S}
    {f : StateExpr S V} {g : StateExpr S W}
    (waiting : ∀ s t, p s → next.bracket f s t → p t ∨ q t)
    (progress : ∀ s t, p s → A.angle g s t → q t)
    (enabled : ∀ s, p s → (A.angle g).enabled s) :
    (conj (.alwaysBracket next f) (weakFair A g)).Entails ((state p).leadsTo (.state q)) :=
  Proofs.Logic.Temporal.TLA.weakFair_progress waiting progress enabled

/-- Formula evaluation commutes with retiming at corresponding instants. -/
theorem holds_retime (p : Formula S) (σ : Behavior S) (r : Retiming) (i : Nat) :
    p.Holds (σ.retime r) i ↔ p.Holds σ (r.index i) :=
  Proofs.Logic.Temporal.TLA.holds_retime p σ r i

theorem sat_stutterInvariant (p : Formula S) : StutterInvariant p.Sat :=
  Proofs.Logic.Temporal.TLA.sat_stutterInvariant p

end Formula

namespace Retiming

/-- Every original edge at or after `r.index i` is reached by an advancing step. -/
theorem crosses (r : Retiming) {i j : Nat} (h : r.index i ≤ j) :
    ∃ k, i ≤ k ∧ r.index k = j ∧ r.index (k + 1) = j + 1 :=
  Proofs.Logic.Temporal.TLA.retiming_crosses r h

end Retiming

namespace StutterEquiv

theorem refl (σ : Behavior S) : StutterEquiv σ σ :=
  Proofs.Logic.Temporal.TLA.stutter_refl σ

theorem retime (σ : Behavior S) (r : Retiming) : StutterEquiv σ (σ.retime r) :=
  Proofs.Logic.Temporal.TLA.stutter_retime σ r

theorem symm {σ τ : Behavior S} (h : StutterEquiv σ τ) : StutterEquiv τ σ :=
  Proofs.Logic.Temporal.TLA.stutter_symm h

theorem trans {σ τ ρ : Behavior S} (h : StutterEquiv σ τ) (h' : StutterEquiv τ ρ) :
    StutterEquiv σ ρ :=
  Proofs.Logic.Temporal.TLA.stutter_trans h h'

theorem map {V : Type v} (f : S → V) {σ τ : Behavior S} (h : StutterEquiv σ τ) :
    StutterEquiv (σ.map f) (τ.map f) :=
  Proofs.Logic.Temporal.TLA.stutter_map f h

theorem suffix_retime (σ : Behavior S) (r : Retiming) (i : Nat) :
    StutterEquiv ((σ.retime r).suffix i) (σ.suffix (r.index i)) :=
  Proofs.Logic.Temporal.TLA.stutter_suffix_retime σ r i

end StutterEquiv

theorem hide_stutterInvariant {V : Type v} (p : Behavior (S × V) → Prop) :
    StutterInvariant (hide p) :=
  Proofs.Logic.Temporal.TLA.hide_stutterInvariant p

/-- Pulling a hiding operand back along a visible-state map commutes with hiding.
The reverse direction uses a common expansion and repeats the witness's hidden
values along its own clock. -/
theorem hide_map_iff {T : Type w} {V : Type v} (f : T → S) {p : Behavior (S × V) → Prop}
    (hp : StutterInvariant p) (σ : Behavior T) :
    hide (fun τ => p (τ.map fun z => (f z.1, z.2))) σ ↔ hide p (σ.map f) :=
  Proofs.Logic.Temporal.TLA.hide_map_iff f hp σ

/-- For stutter-invariant operands, visible hiding agrees with the full-state
clause in Lamport's paper (§8.2, equation 49), using product states. -/
theorem hide_iff_lamport {V : Type v} {p : Behavior (S × V) → Prop} (hp : StutterInvariant p)
    (σ : Behavior (S × V)) :
    hide p (σ.map Prod.fst) ↔
      ∃ ρ τ : Behavior (S × V), StutterEquiv σ ρ ∧ ρ.map Prod.fst = τ.map Prod.fst ∧ p τ :=
  Proofs.Logic.Temporal.TLA.hide_iff_lamport hp σ

end Silmaril.Logic.Temporal.TLA
