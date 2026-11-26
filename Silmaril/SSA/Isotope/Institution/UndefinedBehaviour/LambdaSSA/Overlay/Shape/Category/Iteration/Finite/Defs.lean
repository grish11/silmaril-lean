module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Capture.Thms

/-! # Finite deterministic tables for shaped exact-sum feedback -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

universe u v w x

/-- Terminal results of the observation closure. A fault has its own final
state. Divergence is an ordinary observation, distinct from fresh UB. -/
inductive Result (results states : Nat) where
  | ret (value : Fin results) (state : Fin states)
  | fault (state : Fin states)
  | diverge
  | ub
  deriving DecidableEq

/-- A step either stops or supplies the next coded payload and machine state. -/
inductive Row (points results states : Nat) where
  | stop (result : Result results states)
  | repeat (next : Fin points)

abbrev Table (captures points results states : Nat) :=
  Fin captures → Fin points → Row points results states

variable {captures points results states : Nat}

/-- Scan at most the supplied number of invocations for a terminal row. -/
def search (rows : Fin points → Row points results states) :
    Nat → Fin points → Option (Result results states)
  | 0, _ => none
  | fuel + 1, p =>
    match rows p with
    | .stop outcome => some outcome
    | .repeat q => search rows fuel q

/-- If every invocation within the finite bound repeats, the path cycles. -/
def execute (rows : Fin points → Row points results states) (start : Fin points) :
    Result results states :=
  (search rows points start).getD .diverge

/-- Ordinary singleton results refine by equality. Fresh UB is greatest. -/
def Result.refines (lower upper : Result results states) : Prop :=
  upper = .ub ∨ lower = upper

instance {lower upper : Result results states} : Decidable (lower.refines upper) :=
  inferInstanceAs (Decidable (_ = _ ∨ _ = _))

/-- Decide refinement for every coded capture, seed and initial state. -/
def check (lower upper : Table captures points results states) : Bool :=
  (List.finRange captures).all fun c =>
    (List.finRange points).all fun p => decide ((execute (lower c) p).refines (execute (upper c) p))

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ}

/-- The finite invocation carrier codes supported seed/state pairs and is
closed under the table's repeats. Terminal certificates use injective
result and final-state codes so comparing codes reflects observations. -/
structure Carrier (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))) (X A B : Ty κ)
    (captures points results states : Nat) where
  capture : Fin captures → singlePayload (atomType := M.atomType) X
  invocation : Fin points → singlePayload (atomType := M.atomType) A × M.raw.σ
  result : Fin results ↪ singlePayload (atomType := M.atomType) B
  final : Fin states ↪ M.raw.σ

variable {M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))}

/-- Interpret a result below the lifted top by its unique ordinary outcome. -/
def Result.behaviour (C : Carrier M X A B captures points results states) :
    Result results states → Behaviour 1 M.raw.α M.raw.σ
  | .ret b t => returnPayload (C.result b).val (C.final t)
  | .fault t => WithTop.some {Outcome.fault (C.final t)}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

/-- Interpret a row at the exact-sum exit of the typed step. Tagged returns
keep their final state, and reached UB remains distinct. -/
def Row.behaviour (C : Carrier M X A B captures points results states) :
    Row points results states → Behaviour 1 M.raw.α M.raw.σ
  | .repeat q => returnPayload (.inr (C.invocation q).1.val) (C.invocation q).2
  | .stop (.ret b t) => returnPayload (.inl (C.result b).val) (C.final t)
  | .stop (.fault t) => WithTop.some {Outcome.fault (C.final t)}
  | .stop .diverge => WithTop.some {Outcome.diverge}
  | .stop .ub => ⊤

/-- Every row must match the complete observation of the actual typed overlay
step. The certificate excludes extra outcomes and uncertified successors. -/
def Certified (C : Carrier M X A B captures points results states)
    (r : Region Φ [A, X] [.coprod B A]) (table : Table captures points results states) : Prop :=
  ∀ c p, Shape.denote r ((M.extend (C.capture c).property).extend (C.invocation p).1.property)
    (C.invocation p).2 = (table c p).behaviour C

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
