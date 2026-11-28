module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Soundness

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet pack unpack unpack_pack)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open Syntax (Payload StatePrimitives Primitives)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {A : Syntax.Ty}

private def test [DecidableEq Φ] {n : Nat} (key : Option (Φ × Value Unit)) :
    Primitives Φ n :=
  fun f a s => if key = some (f, a.val) then .fault s else .diverge


theorem observer_local_mismatch_refutes [DecidableEq Φ] (g : HeadObserver.{u,0} S R) (h : HeadObserver.{u,0} S T)
    (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.head p).MatchesWith
      (fun i j => (i, g.returnValue p i) = (j, h.returnValue q j)) (fun _ _ => True) (h.head q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observe prim p 0 ≤ h.observe prim q 0 := by
  cases upper : h.head q with
  | exit j selected =>
    cases selected with
    | true => exact (mismatch (by simp [upper, Head.MatchesWith])).elim
    | false =>
      cases lower : g.head p with
      | exit i marked =>
        refine ⟨test none, ?_⟩
        rw [g.step _ p 0, h.step _ q 0, lower, upper]
        simp only [Head.execute]
        cases marked with
        | true => simp
        | false =>
          intro agrees
          have same : i = j ∧ g.returnValue p i = h.returnValue q j := by
            simpa [WithTop.coe_le_coe] using agrees
          apply mismatch
          simp only [lower, upper, Head.MatchesWith]
          exact Prod.ext same.1 same.2
      | diverge | request =>
        refine ⟨test none, ?_⟩
        rw [g.step _ p 0, h.step _ q 0, lower, upper]
        simp [Head.execute, test, WithTop.coe_le_coe]
  | diverge =>
    cases lower : g.head p with
    | diverge => exact (mismatch (by simp [lower, upper, Head.MatchesWith])).elim
    | exit i marked =>
      refine ⟨test none, ?_⟩
      rw [g.step _ p 0, h.step _ q 0, lower, upper]
      cases marked <;> simp [Head.execute, WithTop.coe_le_coe]
    | request f arg next =>
      refine ⟨test (some (f, arg.val)), ?_⟩
      rw [g.step _ p 0, h.step _ q 0, lower, upper]
      simp [Head.execute, test, WithTop.coe_le_coe]
  | request k operand route =>
    cases lower : g.head p with
    | exit i marked =>
      refine ⟨test none, ?_⟩
      rw [g.step _ p 0, h.step _ q 0, lower, upper]
      cases marked <;> simp [Head.execute, test, WithTop.coe_le_coe]
    | diverge =>
      refine ⟨test (some (k, operand.val)), ?_⟩
      rw [g.step _ p 0, h.step _ q 0, lower, upper]
      simp [Head.execute, test, WithTop.coe_le_coe]
    | request f arg next =>
      have different : ¬ (f = k ∧ arg.val = operand.val) := by
        rintro ⟨rfl, values⟩
        exact mismatch (by rw [lower, upper]; exact ⟨rfl, values, fun _ => trivial⟩)
      refine ⟨test (some (f, arg.val)), ?_⟩
      rw [g.step _ p 0, h.step _ q 0, lower, upper]
      simp [Head.execute, test, different, WithTop.coe_le_coe]

theorem observer_prepend_refutation [DecidableEq Φ] (g : HeadObserver.{u,0} S R) (h : HeadObserver.{u,0} S T)
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.head p = .request f arg next) (upper : h.head q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observe other (next answer.1 answer.2) t ≤ h.observe other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observe prim p 0 ≤ h.observe prim q 0 := by
  let eq := congrArg Payload (S.target f)
  let payload := cast eq.symm (pack answer)
  have decoded : unpack (cast eq payload) = answer := by
    simp only [payload, cast_cast, cast_eq, unpack_pack]
  -- Reserve zero for this query. Mapped answers stay in the suffix image.
  let e : Fin fuel ↪ Fin (fuel + 1) := ⟨Fin.succ, Fin.succ_injective _⟩
  let extended : Primitives Φ (fuel + 1) := fun op input state =>
    Fin.cases
      (if same : f = op ∧ arg.val = input.val then
        .ret (same.1 ▸ payload) (e t)
      else .diverge)
      (fun old => (other op input old).mapState e) state
  have hit : extended f arg 0 = .ret payload (e t) := by
    simp [extended]
  have agree (op : Φ) (input : Payload (instrSrc op)) (old : Fin fuel) :
      extended op input (e old) = (other op input old).mapState e := rfl
  refine ⟨extended, ?_⟩
  rw [g.step extended p 0, h.step extended q 0, lower, upper]
  simp only [Head.execute, hit]
  rw [decoded, g.mapState e other extended agree _ _,
    h.mapState e other extended agree _ _, Behaviour.mapState_le_iff]
  exact bad

theorem payload_local_mismatch_refutes [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry)) (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.control.head a p).MatchesWith
      (fun i j => (g.returnPacket a p i).raw = (h.returnPacket b q j).raw) (fun _ _ => True) (h.control.head b q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  observer_local_mismatch_refutes (payload_observer g a) (payload_observer h b) p q fuel mismatch

theorem payload_prepend_refutation [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry))
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.control.head a p = .request f arg next) (upper : h.control.head b q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observeAt a other (next answer.1 answer.2) t ≤ h.observeAt b other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  observer_prepend_refutation (payload_observer g a) (payload_observer h b) p q lower upper answer other t bad

theorem local_mismatch_refutes [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.head a p).Matches (fun _ _ => True) (h.head b q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 := by
  obtain ⟨prim, bad⟩ := payload_local_mismatch_refutes (Endpoint.unit g) (Endpoint.unit h) a b p q fuel
    (fun good => mismatch ((Endpoint.unit_matches_iff g h a b p q _ _ _).mp good))
  exact ⟨prim, by simpa only [Endpoint.unit_observeAt] using bad⟩

theorem prepend_refutation [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.head a p = .request f arg next) (upper : h.head b q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observeAt a other (next answer.1 answer.2) t ≤ h.observeAt b other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 := by
  have _ := left
  have _ := right
  obtain ⟨prim, fails⟩ := payload_prepend_refutation (Endpoint.unit g) (Endpoint.unit h) a b p q lower upper answer
    other t (by simpa only [Endpoint.unit_observeAt] using bad)
  exact ⟨prim, by simpa only [Endpoint.unit_observeAt] using fails⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
