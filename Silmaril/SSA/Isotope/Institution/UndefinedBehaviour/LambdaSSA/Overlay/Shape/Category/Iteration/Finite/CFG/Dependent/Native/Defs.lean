module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Defs

/-! # Checked readback of native packed overlay CFGs

A native CFG has a constructor entry jump, and each block links a singleton
packed producer to the canonical positional dispatcher. A producer is a
constructor return or a chain of primitive calls written as one-block links.
The expected capture, internal label types and external label types are fixed.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Syntax
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty]
variable {Γ R L P : List Syntax.Ty} {X A B : Syntax.Ty}

abbrev Typed (Φ : Type u) [HasTy Φ Syntax.Ty] (Γ L : List Syntax.Ty) :=
  LambdaSSA.UB.Typed (Φ := Φ) Γ L

/-- The typed producer grammar of native packed blocks. Each link returns
its successful primitive reply to the next producer. -/
inductive Producer (Φ : Type u) [HasTy Φ Syntax.Ty] : List Syntax.Ty → Syntax.Ty → Type u where
  | ret {Γ : List Syntax.Ty} {A : Syntax.Ty} : Expr Γ A → Producer Φ Γ A
  | call {Γ : List Syntax.Ty} {A : Syntax.Ty} (f : Φ) : Expr Γ (instrSrc f) → Producer Φ (instrTrg f :: Γ) A → Producer Φ Γ A

def Producer.program : {Γ : List Syntax.Ty} → Producer Φ Γ A → Program Φ Γ A
  | _, .ret a => .ret a
  | _, .call f a body => .call f a body.program

def jump (i : Fin L.length) (typed : L.get i = A) (a : Expr Γ A) : Typed Φ Γ L :=
  ⟨.br i a.term, .br (typed ▸ List.getElem?_eq_getElem i.isLt) a.typed⟩

/-- A native terminal implementation of ordinary divergence. The inner
unit block silently jumps to itself and never enters a primitive. -/
def diverge : Typed Φ Γ L :=
  let entry : Typed Φ Γ ([.unit] ++ L) :=
    jump (Feedback.internal [.unit] L 0) (internal_type 0) .unit
  let blocks (i : Fin ([.unit] : List Syntax.Ty).length) :
      Typed Φ (([.unit] : List Syntax.Ty).get i :: Γ) ([.unit] ++ L) :=
    jump (Feedback.internal [.unit] L 0) (internal_type 0) .unit
  ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩

def bind (r : Typed Φ Γ [A]) (k : Typed Φ (A :: Γ) L) : Typed Φ Γ L :=
  let next : (i : Fin [A].length) → Typed Φ ([A].get i :: Γ) L :=
    fun i => by obtain rfl := Fin.eq_zero i; exact k
  ⟨nativeLsubst r next, nativeLsubst_hasType r next⟩

def select (left : Typed Φ (A :: .coprod A B :: Γ) L)
    (right : Typed Φ (B :: .coprod A B :: Γ) L) : Typed Φ (.coprod A B :: Γ) L :=
  let source := Program.caseRegion (Φ := Φ) (.var 0 : Expr (.coprod A B :: Γ) (.coprod A B))
  let next : (i : Fin [A, B].length) → Typed Φ ([A, B].get i :: .coprod A B :: Γ) L :=
    Fin.cases (motive := fun i => Typed Φ ([A, B].get i :: .coprod A B :: Γ) L)
      left (fun i => by obtain rfl := Fin.eq_zero i; exact right)
  ⟨nativeLsubst source next, nativeLsubst_hasType source next⟩

def Producer.typed : {Γ : List Syntax.Ty} → Producer Φ Γ A → Typed Φ Γ [A]
  | _, .ret a => Program.returnRegion a
  | _, .call f a body => bind (Program.requestRegion f a) body.typed

def routePacket : {P Γ : List Syntax.Ty} → (target : Fin P.length → Fin L.length) →
    (∀ j, L.get (target j) = P.get j) → Typed Φ (packedExitType P :: Γ) L
  | [], _, _, _ => ⟨LambdaSSA.Region.unpackExits ([] : List Syntax.Ty),
    .cfg (fun _ : Fin 1 => .empty)
      (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))⟩
  | _ :: _, _, target, typed =>
    select (jump (target 0) (typed 0) (.var 0))
      (routePacket (fun j => target j.succ) (fun j => typed j.succ))

/-- The native spelling of a request followed by a positional packet router. -/
def packedRequestTo (f : Φ) (arg : Expr Γ (instrSrc f)) (reply : instrTrg f = packedExitType R)
    (target : Fin R.length → Fin L.length) (typed : ∀ i, L.get (target i) = R.get i) :
    Typed Φ Γ L :=
  bind (Program.requestRegion f arg)
    (cast (congrArg (fun A => Typed Φ (A :: Γ) L) reply.symm) (routePacket target typed))

def route (R L : List Syntax.Ty) {Γ : List Syntax.Ty} :
    Typed Φ (.coprod (packedExitType L) (packedExitType R) :: Γ) (R ++ L) :=
  select (routePacket (exitLabel R L) external_type)
    (routePacket (Feedback.internal R L) internal_type)

/-- The entry argument and each block retain their own label-dependent type. -/
structure Readback (Φ : Type u) [HasTy Φ Syntax.Ty] (X : Syntax.Ty) (R L : List Syntax.Ty) where
  start : Fin R.length
  input : Expr [X] (R.get start)
  producer : (i : Fin R.length) →
    Producer Φ [R.get i, X] (.coprod (packedExitType L) (packedExitType R))

def Readback.blocks (w : Readback Φ X R L) : Blocks Φ X R L :=
  ⟨fun i => (w.producer i).program⟩

def Readback.entry (w : Readback Φ X R L) : Typed Φ [X] (R ++ L) :=
  jump (Feedback.internal R L w.start) (internal_type w.start) w.input

def Readback.routed (w : Readback Φ X R L) (i : Fin R.length) :
    Typed Φ [R.get i, X] (R ++ L) :=
  bind (w.producer i).typed (route R L)

/-- Re-emit the actual native recursive CFG, with exactly the supplied label
positions and their native routing syntax. -/
def Readback.typed (w : Readback Φ X R L) : Typed Φ [X] L :=
  ⟨nativeFeedback w.entry w.routed, nativeFeedback_hasType w.entry w.routed⟩

def readExpr : {Γ : List Syntax.Ty} → (A : Syntax.Ty) → LambdaSSA.Tm Φ → Option (Expr Γ A)
  | Γ, A, .var n => do
    if bound : n < Γ.length then
      let i : Fin Γ.length := ⟨n, bound⟩
      if same : Γ.get i = A then some (same ▸ Expr.var i) else none
    else none
  | _, .unit, .unit => some .unit
  | _, .product A B, .pair a b => Expr.pair <$> readExpr A a <*> readExpr B b
  | _, .coprod A _, .inl a => Expr.inl <$> readExpr A a
  | _, .coprod _ B, .inr b => Expr.inr <$> readExpr B b
  | _, _, _ => none

/-- The offset records the singleton exit past the local call binders. -/
def readProducer {A : Syntax.Ty} :
    {Γ : List Syntax.Ty} → Nat → LambdaSSA.Region Φ → Option (Producer Φ Γ A)
  | Γ, offset, .br i a =>
    if i = offset then
      match readExpr (Γ := Γ) A a with
      | some arg => some (.ret arg)
      | none => none
    else none
  | Γ, offset, .cfg (.br 0 (.op f arg)) 1 blocks =>
    match readExpr (Γ := Γ) (instrSrc f) arg with
    | some a => (readProducer (offset + 1) (blocks 0)).map (Producer.call f a)
    | none => none
  | _, _, _ => none

def readFamily : {n : Nat} → {β : Fin n → Type u} →
    ((i : Fin n) → Option (β i)) → Option ((i : Fin n) → β i)
  | 0, _, _ => some (fun i => i.elim0)
  | _ + 1, _, read => do
    let first ← read 0
    let rest ← readFamily (fun i => read i.succ)
    pure (Fin.cases first rest)

/-- Read the entry and producers. The subsequent whole-syntax check in
`recognize` verifies the dispatchers and label offsets. -/
def propose (R L : List Syntax.Ty) (raw : LambdaSSA.Region Φ) : Option (Readback Φ X R L) := do
  match raw with
  | .cfg (.br i arg) n blocks =>
    if arity : R.length = n then
      if inRange : i < R.length then
        let start : Fin R.length := ⟨i, inRange⟩
        match readExpr (Γ := [X]) (R.get start) arg with
        | none => none
        | some input => do
          let producer ← readFamily
            (β := fun j => Producer Φ [R.get j, X] (.coprod (packedExitType L) (packedExitType R))) fun j =>
            match blocks (j.cast arity) with
            | .cfg source 1 _ => readProducer 0 source
            | _ => none
          some ⟨start, input, producer⟩
      else none
    else none
  | _ => none

variable {captures seeds results states : Nat}

/-- Run the generated block table from this CFG's actual entry expression
and label. The table is evaluated under the coded capture. -/
def Readback.execute (w : Readback Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) : Result results states :=
  let env := emptyBindings.push (C.capture c)
  let start := C.invocation.symm (⟨w.start, w.input.eval env⟩, s)
  FiniteIteration.execute (w.blocks.generate C prim c) start

/-- Compare the chosen entry of each successful readback at every coded
capture and initial state, using the existing finite result order. -/
def check (left right : Readback Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) : Bool :=
  (List.finRange captures).all fun c =>
    (List.finRange states).all fun s => decide ((left.execute C prim c s).refines (right.execute C prim c s))

variable [DecidableEq Φ]

/-- Compare the native constructors in the emitted syntax, including all
finite tables. This compares syntax rather than following control-flow edges. -/
def sameRegion (r t : LambdaSSA.Region Φ) : Bool :=
  match r, t with
  | .br i a, .br j b => decide (i = j) && decide (a = b)
  | .let₁ a body, .let₁ b body' => decide (a = b) && sameRegion body body'
  | .case a left right, .case b left' right' =>
    decide (a = b) && sameRegion left left' && sameRegion right right'
  | .cfg e n blocks, .cfg e' m blocks' =>
    if arity : n = m then
      sameRegion e e' && (List.finRange n).all (fun i => sameRegion (blocks i) (blocks' (i.cast arity)))
    else false
  | _, _ => false
termination_by structural r

/-- Read the typed producers from the native CFG and verify the exact
re-emission of the whole input, including the positional dispatchers. -/
def recognize (R : List Syntax.Ty) (raw : Typed Φ [X] L) : Option (Readback Φ X R L) := do
  let candidate ← propose R L raw.val
  if sameRegion raw.val candidate.typed.val then some candidate else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
