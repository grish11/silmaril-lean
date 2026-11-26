module

public import Silmaril.SSA.PEG.Rules.Defs
import Silmaril.Proofs.SSA.PEG.Rules.Local
import Silmaril.Proofs.SSA.PEG.Rules.Invariance
import Silmaril.Proofs.SSA.PEG.Rules.Rewrites

/-! # Sound invariance and guarded Figure 11 rewrites -/

public section

namespace Silmaril.SSA.PEG.Rules

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ins : List (Ty Data)} {out : Ty Data} {n l : Nat}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,x} P}
variable {values : g.Valuation m} {env : Tuple m.Value params}

theorem invariantAt_notTheta {loop : Fin l} {a : Fin n} (h : InvariantAt g loop a) :
    (g.node a).label.thetaLoop ≠ some loop :=
  Proofs.invariantAt_notTheta h

theorem invariantAt_step {loop : Fin l} {a b : Fin n} {kind : EdgeKind (Fin l)}
    (h : InvariantAt g loop a) (edge : InvarianceEdge g loop a kind b) : InvariantAt g loop b :=
  Proofs.invariantAt_step h edge

theorem invariantAt_iff {loop : Fin l} {a : Fin n} : InvariantAt g loop a ↔
    ((g.node a).label.thetaLoop ≠ some loop ∧
      ∀ {b kind}, InvarianceEdge g loop a kind b → InvariantAt g loop b) :=
  Proofs.invariantAt_iff

/-- Together with the closure laws, this identifies `InvariantAt` as the largest predicate
satisfying Definition 5.2. -/
theorem invariantAt_largest {loop : Fin l} (p : Fin n → Prop)
    (noTheta : ∀ a, p a → (g.node a).label.thetaLoop ≠ some loop)
    (closed : ∀ {a b kind}, InvarianceEdge g loop a kind b → p a → p b)
    {a : Fin n} (ha : p a) : InvariantAt g loop a :=
  Proofs.invariantAt_largest p noTheta closed ha

/-- Definition 5.2 is sound on well-founded Figure 11 demands, including cyclic graphs
and streams with undefined entries. -/
theorem invariant_sound (wf : WellFounded g.Demand) (solves : g.Solves m env values)
    {loop : Fin l} {r : Ref g.sort out} (guard : InvariantAt g loop r.id) :
    Invariant values loop r :=
  Proofs.invariant_sound wf solves guard

theorem denote_invariant (wf : WellFounded g.Demand) {loop : Fin l} {r : Ref g.sort out}
    (guard : InvariantAt g loop r.id) : Invariant (g.denote m env wf) loop r :=
  invariant_sound wf (g.denote_solves m env wf) guard

/-- Connect typed rule conclusions to the same-sort vertex stream equality used by
E-PEG merge receipts. -/
theorem streamEq_iff_vertex (a b : Ref g.sort out) :
    StreamEq values a b ↔ (g.sort a.id = g.sort b.id ∧ ∀ i, HEq (values (a.id, i)) (values (b.id, i))) :=
  Proofs.streamEq_iff_vertex a b

/-- Read an actual row equation through the typed references in its operand tuple. -/
theorem at_label (solves : g.Solves m env values) {r : Ref g.sort out}
    {label : Label P params (Fin l) ins out} {args : Tuple (Ref g.sort) ins}
    (node : HasNode r label args) (i : Index l) :
    readRef values r i = label.interpret m env i
      (fun slot j _ => readRef values (args.get (portAt ins slot)) j) :=
  Proofs.at_label solves node i

theorem phi_at (solves : g.Solves m env values) {r yes no : Ref g.sort out}
    {cond : Ref g.sort .bool} (node : HasNode r .phi (.cons cond (.cons yes (.cons no .nil))))
    (i : Index l) : readRef values r i = (readRef values cond i).elim none
      (fun flag => if flag.down then readRef values yes i else readRef values no i) :=
  Proofs.phi_at solves node i

theorem theta_zero (solves : g.Solves m env values) {r initial feedback : Ref g.sort out}
    {loop : Fin l} (node : HasNode r (.theta loop) (.cons initial (.cons feedback .nil)))
    {i : Index l} (atZero : i loop = 0) : readRef values r i = readRef values initial i :=
  Proofs.theta_zero solves node atZero

theorem theta_succ (solves : g.Solves m env values) {r initial feedback : Ref g.sort out}
    {loop : Fin l} (node : HasNode r (.theta loop) (.cons initial (.cons feedback .nil)))
    {i : Index l} {k : Nat} (atSucc : i loop = k + 1) :
    readRef values r i = readRef values feedback (i.set loop k) :=
  Proofs.theta_succ solves node atSucc

theorem eval_at (solves : g.Solves m env values) {r source : Ref g.sort out}
    {count : Ref g.sort .count} {loop : Fin l}
    (node : HasNode r (.eval loop) (.cons source (.cons count .nil))) (i : Index l) :
    readRef values r i = (readRef values count i).elim none
      (fun k => monotonize (fun j => readRef values source (i.set loop j)) k.down) :=
  Proofs.eval_at solves node i

theorem pass_at (solves : g.Solves m env values) {r : Ref g.sort .count}
    {cond : Ref g.sort .bool} {loop : Fin l} (node : HasNode r (.pass loop) (.cons cond .nil))
    (i : Index l) : readRef values r i =
      (firstTrue (fun j => (readRef values cond (i.set loop j)).map ULift.down)).map ULift.up :=
  Proofs.pass_at solves node i

theorem unary_at (solves : g.Solves m env values) {r : Ref g.sort out}
    {ty : Ty Data} {arg : Ref g.sort ty} {op : P [ty] out}
    (node : HasNode r (.op op) (.cons arg .nil)) (i : Index l) :
    readRef values r i = (readRef values arg i).bind (fun a => m.run op (.cons a .nil)) :=
  Proofs.unary_at solves node i

section Phi
variable {r yes no : Ref g.sort out} {cond : Ref g.sort .bool}

/-- Select the true branch under a defined true guard. -/
theorem phi_true (solves : g.Solves m env values)
    (node : HasNode r .phi (.cons cond (.cons yes (.cons no .nil))))
    (guard : ∀ i, readRef values cond i = some ⟨true⟩) : StreamEq values r yes :=
  Proofs.phi_true solves node guard

/-- Select the false branch under a defined false guard. -/
theorem phi_false (solves : g.Solves m env values)
    (node : HasNode r .phi (.cons cond (.cons yes (.cons no .nil))))
    (guard : ∀ i, readRef values cond i = some ⟨false⟩) : StreamEq values r no :=
  Proofs.phi_false solves node guard

/-- Appendix A.1 equal-branch elimination with a defined condition. -/
theorem phi_same_of_defined (solves : g.Solves m env values)
    {a : Ref g.sort out}
    (node : HasNode r .phi (.cons cond (.cons a (.cons a .nil))))
    (defined : ∀ i, (readRef values cond i).isSome) : StreamEq values r a :=
  Proofs.phi_same_of_defined solves node defined

/-- Appendix A.1 repeated-condition simplification, including a bottom condition. -/
theorem phi_nested_true (solves : g.Solves m env values)
    {r' inner t f fallback : Ref g.sort out}
    (outer : HasNode r .phi (.cons cond (.cons inner (.cons fallback .nil))))
    (branch : HasNode inner .phi (.cons cond (.cons t (.cons f .nil))))
    (simple : HasNode r' .phi (.cons cond (.cons t (.cons fallback .nil)))) : StreamEq values r r' :=
  Proofs.phi_nested_true solves outer branch simple

end Phi

/-- A defined zero count samples index zero with an empty prefix. -/
theorem eval_zero (solves : g.Solves m env values)
    {r source : Ref g.sort out} {count : Ref g.sort .count} {loop : Fin l}
    (node : HasNode r (.eval loop) (.cons source (.cons count .nil))) {i : Index l}
    (atZero : readRef values count i = some ⟨0⟩) :
    readRef values r i = readRef values source (i.set loop 0) :=
  Proofs.eval_zero solves node atZero

/-- Section 5.3 base-sample rewrite through theta. -/
theorem eval_zero_theta (solves : g.Solves m env values)
    {r r' theta initial feedback : Ref g.sort out} {count : Ref g.sort .count}
    {loop : Fin l} (evalTheta : HasNode r (.eval loop) (.cons theta (.cons count .nil)))
    (thetaNode : HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (evalInitial : HasNode r' (.eval loop) (.cons initial (.cons count .nil)))
    (zero : ∀ i, readRef values count i = some ⟨0⟩) : StreamEq values r r' :=
  Proofs.eval_zero_theta solves evalTheta thetaNode evalInitial zero

/-- Section 5.3 and Appendix A.1 invariant sample elimination with a defined count. -/
theorem eval_invariant (solves : g.Solves m env values)
    {r source : Ref g.sort out} {count : Ref g.sort .count} {loop : Fin l}
    (node : HasNode r (.eval loop) (.cons source (.cons count .nil)))
    (invariant : Invariant values loop source) (defined : ∀ i, (readRef values count i).isSome) :
    StreamEq values r source :=
  Proofs.eval_invariant solves node invariant defined

/-- Section 5.3 and Appendix A.1 self-feedback elimination, allowing the feedback
stream to be identified with the theta stream by a previously justified equality. -/
theorem theta_self (solves : g.Solves m env values)
    {r initial feedback : Ref g.sort out} {loop : Fin l}
    (node : HasNode r (.theta loop) (.cons initial (.cons feedback .nil)))
    (cycle : StreamEq values feedback r) (invariant : Invariant values loop initial) :
    StreamEq values r initial :=
  Proofs.theta_self solves node cycle invariant

/-- Section 5.3 immediate exit from a defined true first sample. -/
theorem pass_zero (solves : g.Solves m env values)
    {r : Ref g.sort .count} {cond : Ref g.sort .bool} {loop : Fin l}
    (node : HasNode r (.pass loop) (.cons cond .nil)) {i : Index l}
    (first : readRef values cond (i.set loop 0) = some ⟨true⟩) : readRef values r i = some ⟨0⟩ :=
  Proofs.pass_zero solves node first

/-- The Figure 8 pass recurrence with a certified one-iteration suffix stream. -/
theorem pass_peel (solves : g.Solves m env values)
    {r backPass : Ref g.sort .count} {predicate suffix : Ref g.sort .bool}
    {loop : Fin l} (passMain : HasNode r (.pass loop) (.cons predicate .nil))
    (passSuffix : HasNode backPass (.pass loop) (.cons suffix .nil)) {i : Index l}
    (samples : ∀ k, readRef values predicate (i.set loop (k + 1)) = readRef values suffix (i.set loop k)) :
    readRef values r i = (readRef values predicate (i.set loop 0)).elim none
      (fun flag => if flag.down then some ⟨0⟩ else (readRef values backPass i).map (fun k => ⟨k.down + 1⟩)) :=
  Proofs.pass_peel solves passMain passSuffix samples

/-- Figure 8(b–c) as a stream equality of actual pass and phi rows. The suffix stream
is supplied by the caller, and the successor obeys the explicit count contract. -/
theorem pass_peel_phi (solves : g.Solves m env values)
    {r r' backPass shifted countZero : Ref g.sort .count}
    {predicate suffix first : Ref g.sort .bool} {loop : Fin l} {op : P [.count] .count}
    (passMain : HasNode r (.pass loop) (.cons predicate .nil))
    (passSuffix : HasNode backPass (.pass loop) (.cons suffix .nil))
    (sampleFirst : HasNode first (.eval loop) (.cons predicate (.cons countZero .nil)))
    (succNode : HasNode shifted (.op op) (.cons backPass .nil))
    (select : HasNode r' .phi (.cons first (.cons countZero (.cons shifted .nil))))
    (zero : ∀ i, readRef values countZero i = some ⟨0⟩)
    (successor : ∀ k : m.Value .count, m.run op (.cons k .nil) = some ⟨k.down + 1⟩)
    (samples : ∀ (i : Index l) k, readRef values predicate (i.set loop (k + 1)) =
      readRef values suffix (i.set loop k)) : StreamEq values r r' :=
  Proofs.pass_peel_phi solves passMain passSuffix sampleFirst succNode select zero successor samples

/-- Section 5.3 false-initial theta shifts the pass result by one, retaining bottom. -/
theorem pass_theta_false (solves : g.Solves m env values)
    {r backPass : Ref g.sort .count} {theta initial feedback : Ref g.sort .bool}
    {loop : Fin l} (passTheta : HasNode r (.pass loop) (.cons theta .nil))
    (thetaNode : HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (passFeedback : HasNode backPass (.pass loop) (.cons feedback .nil))
    (initialFalse : ∀ i : Index l, readRef values initial (i.set loop 0) = some ⟨false⟩) (i : Index l) :
    readRef values r i = (readRef values backPass i).map (fun k => ⟨k.down + 1⟩) :=
  Proofs.pass_theta_false solves passTheta thetaNode passFeedback initialFalse i

/-- The false-initial shift as an equality of actual graph vertices, using an
explicit successor interpretation for defined counts. -/
theorem pass_theta_false_succ (solves : g.Solves m env values)
    {r r' backPass : Ref g.sort .count}
    {theta initial feedback : Ref g.sort .bool} {loop : Fin l} {op : P [.count] .count}
    (passTheta : HasNode r (.pass loop) (.cons theta .nil))
    (thetaNode : HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (passFeedback : HasNode backPass (.pass loop) (.cons feedback .nil))
    (succNode : HasNode r' (.op op) (.cons backPass .nil))
    (initialFalse : ∀ i : Index l, readRef values initial (i.set loop 0) = some ⟨false⟩)
    (successor : ∀ k : m.Value .count, m.run op (.cons k .nil) = some ⟨k.down + 1⟩) :
    StreamEq values r r' :=
  Proofs.pass_theta_false_succ solves passTheta thetaNode passFeedback succNode initialFalse successor

end Silmaril.SSA.PEG.Rules
