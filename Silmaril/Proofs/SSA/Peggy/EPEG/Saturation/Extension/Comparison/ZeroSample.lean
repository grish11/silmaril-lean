module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Embedding
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n k l : Nat}
variable {small : State P params results n l} {large : State P params results k l}
variable {site : Fin n} {zero : P [] .count}

private theorem ofNodes_row {g : Graph P params results n l} {t : Ty Data} (loop : Fin l)
    (site theta initial feedback : Ref g.sort t) (count : Ref g.sort .count)
    (evalNode : Rules.HasNode site (.eval loop) (.cons theta (.cons count .nil)))
    (thetaNode : Rules.HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (countNode : Rules.HasNode count (.op zero) .nil) :
    (ZeroSample.ofNodes loop site theta initial feedback count evalNode thetaNode countNode).row =
      ⟨_, t, .eval loop, .cons initial (.cons count .nil)⟩ := by
  obtain ⟨i, eq⟩ := site
  subst t
  rfl

theorem transport_row (e : Embedding small large) (found : ZeroSample small.graph site zero) :
    (found.transport e).row = e.mapRow found.row :=
  ofNodes_row _ _ _ _ _ _ _ _ _

private theorem seed_compare (e : Embedding small large) (row : Row small.graph)
    {a b : Fin (n + 1)} (joined : Row.liftClasses small.classes a = Row.liftClasses small.classes b) :
    Row.liftClasses large.classes ((e.appendVertices row).address a) =
      Row.liftClasses large.classes ((e.appendVertices row).address b) := by
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · rfl
  · rename_i b
    have bad : Fin.last n = (small.classes b).castSucc := by simpa [Row.liftClasses] using joined
    exact (Fin.ne_of_lt (small.classes b).castSucc_lt_last bad.symm).elim
  · rename_i a
    have bad : (small.classes a).castSucc = Fin.last n := by simpa [Row.liftClasses] using joined
    exact (Fin.ne_of_lt (small.classes a).castSucc_lt_last bad).elim
  · rename_i a b
    have same : small.classes a = small.classes b := Fin.castSucc_inj.mp
      (by simpa only [Row.liftClasses, Fin.lastCases_castSucc] using joined)
    rw [append_address_old, append_address_old]
    simpa only [Row.liftClasses, Fin.lastCases_castSucc, Fin.castSucc_inj] using e.classes a b same

/-- Containment of the seed pairs and the new conclusion suffices to
contain all pairs introduced by a single whole-class merge. -/
private theorem merge_compare {a b : Fin (n + 1)} {c : Classes (n + 1)} {d : Classes (k + 1)}
    (f : Fin (n + 1) → Fin (k + 1))
    (seed : ∀ i j, c i = c j → d (f i) = d (f j)) (conclusion : d (f a) = d (f b))
    {i j : Fin (n + 1)} (joined : c.merge a b i = c.merge a b j) : d (f i) = d (f j) := by
  let pick := fun v => if c v = c b then a else v
  have read (v) : d (f v) = d (f (pick v)) := by
    by_cases h : c v = c b
    · exact (seed v b h).trans (by simpa [pick, h] using conclusion.symm)
    · simp [pick, h]
  exact (read i).trans ((seed (pick i) (pick j) joined).trans (read j).symm)

private theorem merge_form (found : ZeroSample small.graph site zero) :
    found.step.apply.classes = (Row.liftClasses small.classes).merge site.castSucc (Fin.last n) := by
  have distinct : (small.classes site).castSucc ≠ Fin.last n :=
    Fin.ne_of_lt (small.classes site).castSucc_lt_last
  simp [Step.apply, ZeroSample.step, ZeroSample.equation, Saturation.run,
    Saturation.takeEnabled, Saturation.Obligation.enabled, Saturation.Obligation.endpoints,
    Saturation.Obligation.check, Saturation.Obligation.merge, GuardedEquation.check,
    Row.liftClasses, distinct]

theorem simulate_classes (e : Embedding small large) (found : ZeroSample small.graph site zero)
    (a b : Fin (n + 1)) (joined : found.step.apply.classes a = found.step.apply.classes b) :
    (found.transport e).step.apply.classes ((e.appendVertices found.row).address a) =
      (found.transport e).step.apply.classes ((e.appendVertices found.row).address b) := by
  rw [merge_form found] at joined
  apply merge_compare _ _ _ joined
  · intro i j same
    apply Saturation.run_extends 1 [.guarded (found.transport e).equation] (Row.liftClasses large.classes)
    exact seed_compare e found.row same
  · rw [append_address_old, append_address_fresh]
    exact (found.transport e).equates

theorem simulate (e : Embedding small large) (found : ZeroSample small.graph site zero) :
    ∃ mapped : Embedding found.step.apply (found.transport e).step.apply,
      ∀ i, mapped.vertices.address i = (e.appendVertices found.row).address i := by
  let cs := found.step.apply.classes
  let ds := (found.transport e).step.apply.classes
  have build (row : Row large.graph) (eq : row = e.mapRow found.row) :
      ∃ mapped : Embedding found.step.apply (⟨row.append, ds⟩ : State P params results (k + 1) l),
        ∀ i, mapped.vertices.address i = (e.appendVertices found.row).address i := by
    subst row
    exact ⟨append e found.row cs ds (simulate_classes e found),
      append_address e found.row cs ds (simulate_classes e found)⟩
  exact build _ (transport_row e found)

private theorem typedNode_eq {g : Graph P params results n l} {ts : List (Ty Data)} {t : Ty Data}
    {r : Ref g.sort t} {label : Label P params (Fin l) ts t} {args : Tuple (Ref g.sort) ts}
    (shape : Rules.HasNode r label args) : typedNode r = Node.ofLabel label args :=
  eq_of_heq ((eqRec_heq r.typed _).trans shape)

theorem matchAt_of_witness [DecidableEq (P [] .count)] {g : Graph P params results n l}
    (found : ZeroSample g site zero) : ZeroSample.matchAt site zero = some found := by
  have evalEq : g.node site =
      Node.ofLabel (.eval found.loop) (.cons found.theta (.cons found.count .nil)) :=
    eq_of_heq found.evalNode
  have evalAt (node) (h : g.node site = node) :
      ZeroSample.matchAt (g := g) site zero = matchEval site zero node h := by subst node; rfl
  rw [evalAt _ evalEq]
  change matchTheta site zero found.loop found.theta found.count found.evalNode
    (typedNode found.theta) rfl = some found
  have thetaAt (node) (h : typedNode found.theta = node) :
      matchTheta site zero found.loop found.theta found.count found.evalNode (typedNode found.theta) rfl =
        matchTheta site zero found.loop found.theta found.count found.evalNode node h := by
    subst node
    rfl
  rw [thetaAt _ (typedNode_eq found.thetaNode)]
  change (if _same : found.loop = found.loop then
    (do let literal ← matchCount zero found.count (typedNode found.count) rfl
        pure ⟨found.loop, found.theta, found.initial, found.feedback, found.count,
          found.evalNode, found.thetaNode, literal.down⟩)
    else none) = some found
  rw [dite_eq_left rfl]
  have countAt (node) (h : typedNode found.count = node) :
      matchCount zero found.count (typedNode found.count) rfl = matchCount zero found.count node h := by
    subst node
    rfl
  rw [countAt _ (typedNode_eq found.countNode)]
  change (do let literal ← (if _same : zero = zero then some (PLift.up found.countNode) else none)
             pure ⟨found.loop, found.theta, found.initial, found.feedback, found.count,
               found.evalNode, found.thetaNode, literal.down⟩) = some found
  rw [dite_eq_left rfl]
  cases found
  rfl

theorem zeroSample_inflationary (zero : P [] .count) :
    Inflationary (params := params) (results := results) (l := l) (ZeroSampleAnalysis zero) := by
  rintro source target (rfl | ⟨_, found, rfl⟩)
  · exact ⟨refl target.2⟩
  · exact ⟨step found.step⟩

theorem zeroSample_monotone (zero : P [] .count) :
    MonotoneAnalysis (params := params) (results := results) (l := l) (ZeroSampleAnalysis zero) := by
  rintro source target sourceNext ⟨e⟩ (rfl | ⟨site, found, rfl⟩)
  · exact ⟨target, .inl rfl, ⟨e⟩⟩
  · obtain ⟨mapped, _⟩ := simulate e found
    exact ⟨⟨_, (found.transport e).step.apply⟩, .inr ⟨e.vertices.address site, _, rfl⟩, ⟨mapped⟩⟩

theorem zeroSample_progress (found : ZeroSample small.graph site zero) :
    NormalForms.Progress Comparable (ZeroSampleFamily zero) ⟨n, small⟩ ⟨n + 1, found.step.apply⟩ := by
  refine ⟨⟨(), .inr ⟨site, found, rfl⟩⟩, ?_⟩
  rintro ⟨back⟩
  exact (Nat.not_succ_le_self n) (embedding_size_le back)

theorem zeroSample_grows (found : ZeroSample small.graph site zero) (extra : Nat) :
    ∃ target, NormalForms.Reachable (ZeroSampleFamily zero) ⟨n, small⟩ target ∧ target.1 = n + extra := by
  induction extra generalizing n with
  | zero => exact ⟨⟨n, small⟩, .refl, rfl⟩
  | succ extra ih =>
    let e := step found.step
    obtain ⟨target, trace, size⟩ := ih (found.transport e)
    exact ⟨target, Relation.ReflTransGen.head (zeroSample_progress found).1 trace,
      size.trans (Nat.succ_add n extra)⟩

theorem zeroSample_no_stable (found : ZeroSample small.graph site zero)
    {target : Output P params results l}
    (trace : NormalForms.Reachable (ZeroSampleFamily zero) ⟨n, small⟩ target) :
    ¬ NormalForms.Stable Comparable (ZeroSampleFamily zero) target := by
  have matchSurvives (s : Output P params results l)
      (path : NormalForms.Reachable (ZeroSampleFamily zero) ⟨n, small⟩ s) :
      ∃ i, Nonempty (ZeroSample s.2.graph i zero) := by
    induction path with
    | refl => exact ⟨site, ⟨found⟩⟩
    | tail _ reason ih =>
      obtain ⟨_, rfl | ⟨_, rule, rfl⟩⟩ := reason
      · exact ih
      · obtain ⟨i, ⟨earlier⟩⟩ := ih
        let e := step rule.step
        exact ⟨e.vertices.address i, ⟨earlier.transport e⟩⟩
  obtain ⟨_, ⟨rule⟩⟩ := matchSurvives target trace
  exact fun stable => (zeroSample_progress rule).2 (stable (zeroSample_progress rule).1)

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison
