module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Institution.Observational (Model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

universe u w x

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)]
variable {Γ K R L P : List (Silmaril.Ty Empty)} {X A B : Silmaril.Ty Empty}

private abbrev Agrees (r t : Region Φ Γ L) : Prop :=
  ∀ (M : Model.{u,w,x} Φ Γ.length) (s : M.σ), denote r M s = denote t M s

private theorem linked_agrees {r : Region Φ Γ K}
    {k : (i : Fin K.length) → Region Φ (K.get i :: Γ) L}
    {p : Typed Φ Γ K} {q : (i : Fin K.length) → Typed Φ (K.get i :: Γ) L}
    (hp : Agrees.{u,w,x} r (.native p)) (hq : ∀ i, Agrees.{u,w,x} (k i) (.native (q i))) :
    Agrees.{u,w,x} (.lsubst r k) (.native ⟨nativeLsubst p q, nativeLsubst_hasType p q⟩) := by
  intro M s
  calc
    _ = denote (.lsubst (.native p) (fun i => .native (q i))) M s := by
      rw [denote, denote, hp M s]
      congr 1
      funext i a mid
      exact hq i (extendModel M a) mid
    _ = _ := denote_native_lsubst p q M s

private theorem bind_agrees (r : Region Φ Γ [A]) (k : Region Φ (A :: Γ) L)
    (p : Typed Φ Γ [A]) (q : Typed Φ (A :: Γ) L)
    (hp : Agrees.{u,w,x} r (.native p)) (hq : Agrees.{u,w,x} k (.native q)) :
    Agrees.{u,w,x} (Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.bindOne r k) (.native (bind p q)) := by
  apply linked_agrees hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact hq

private theorem select_agrees (l : Region Φ (A :: .coprod A B :: Γ) L)
    (r : Region Φ (B :: .coprod A B :: Γ) L)
    (p : Typed Φ (A :: .coprod A B :: Γ) L) (q : Typed Φ (B :: .coprod A B :: Γ) L)
    (hl : Agrees.{u,w,x} l (.native p)) (hr : Agrees.{u,w,x} r (.native q)) :
    Agrees.{u,w,x} (Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.select l r) (.native (select p q)) := by
  apply linked_agrees (fun _ _ => rfl)
  intro i
  refine Fin.cases hl (fun j => ?_) i
  obtain rfl := Fin.eq_zero j
  exact hr

private theorem producer_agrees (p : Producer Φ Γ A) :
    Agrees.{u,w,x} p.program.region (.native p.typed) := by
  induction p with
  | ret a => exact fun _ _ => rfl
  | call f a body ih => exact bind_agrees _ _ _ _ (fun _ _ => rfl) ih

private theorem packet_routes_agree (target : Fin P.length → Fin L.length)
    (typed : ∀ i, L.get (target i) = P.get i) :
    Agrees.{u,w,x} (Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.routePacket (Γ := Γ) (Φ := Φ) target typed)
      (.native (routePacket target typed)) := by
  induction P generalizing Γ with
  | nil => exact fun _ _ => rfl
  | cons A P ih =>
    exact select_agrees _ _ _ _ (fun _ _ => rfl) (ih (fun j => target j.succ) (fun j => typed j.succ))

private theorem cast_routes {A' A : Silmaril.Ty Empty} (h : A' = A)
    (r : Region Φ (A :: Γ) L) (q : Typed Φ (A :: Γ) L) (agree : Agrees.{u,w,x} r (.native q)) :
    Agrees.{u,w,x}
      (Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.castHead h r)
      (.native (cast (congrArg (fun T => Typed Φ (T :: Γ) L) h.symm) q)) := by
  cases h
  exact agree

theorem packedRequestTo_agrees (f : Φ)
    (arg : Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.Expr Γ (instrSrc f))
    (reply : instrTrg f = Silmaril.Isotope.LambdaSSA.Region.packedExitType R)
    (target : Fin R.length → Fin L.length) (typed : ∀ i, L.get (target i) = R.get i) :
    ∀ (M : Model.{u,w,x} Φ Γ.length) (s : M.σ),
      denote (Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.packedRequestTo
        f arg reply target typed) M s =
      denote (.native (packedRequestTo f arg reply target typed)) M s :=
  bind_agrees _ _ _ _ (fun _ _ => rfl) (cast_routes reply _ _ (packet_routes_agree target typed))

private theorem routes_agree :
    Agrees.{u,w,x} (Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.route (Γ := Γ) (Φ := Φ) R L) (.native (route R L)) :=
  select_agrees _ _ _ _ (packet_routes_agree _ _) (packet_routes_agree _ _)

theorem routed_agrees (w : Readback Φ X R L) (i : Fin R.length)
    (M : Model.{u,w,x} Φ [R.get i, X].length) (s : M.σ) :
    denote (w.blocks.routed i) M s = denote (.native (w.routed i)) M s :=
  bind_agrees _ _ _ _ (producer_agrees (w.producer i)) routes_agree M s

theorem readback_agrees (w : Readback Φ X R L) (M : Model.{u,w,x} Φ [X].length) (s : M.σ) :
    denote (w.blocks.region w.start w.input) M s = denote (.native w.typed) M s := by
  let entry : Region Φ [X] (R ++ L) := .native w.entry
  have same : feedbackRun entry w.blocks.routed M =
      feedbackRun entry (fun i => .native (w.routed i)) M := by
    funext point
    cases point with
    | entry => rfl
    | block i a mid => exact routed_agrees w i (extendModel M a) mid
  calc
    _ = denote (.feedback entry (fun i => .native (w.routed i))) M s :=
      congrArg (fun run => Feedback.close run (.entry s)) same
    _ = _ := denote_native_feedback w.entry w.routed M s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
