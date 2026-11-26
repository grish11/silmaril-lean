module

import Silmaril.Semantics.ITree.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Thms
import Silmaril.Semantics.ITree.VisiblePrefix.Thms
import Silmaril.SSA.Isotope.LetIter.RequestFeedback.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Cyclic.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Structured.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Context.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.EffectWeakening.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Thms
import Silmaril.SSA.Isotope.LetParCase.Thms
import Mathlib.Control.Monad.Writer

/-! A mixed weak interaction-tree model and original-bound endpoint reflection
for the open unary source fragment. -/

namespace LetParRegression

/-! Lower-tier embedding audits and effectful parallel interpretation regressions. -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.Parallel Silmaril.Isotope.Semantics

private inductive Instr where
  | emit (tag : Nat)

private instance : HasTy Instr (Ty Unit) where
  src _ := .unit
  trg _ := .base ()

private instance : HasEff Instr Bool where
  eff _ := true

private abbrev D := Ty.denote (fun _ : Unit => Nat)
private abbrev Γ : Ctx Empty (Ty Unit) := .nil
private abbrev number : Ty Unit := .base ()

private abbrev count (α : Type) := Writer Nat α
private instance : Monad count := WriterT.monad 0 Nat.add

private def countInstr : InstructionModel D Instr count where
  eval
    | .emit tag, _ => WriterT.mk (tag, tag)

/-- Combine the branch logs by addition while retaining the order of the result values. -/
private def countPar : ParOp count := fun a b =>
  WriterT.mk ((a.run.1, b.run.1), a.run.2 + b.run.2)

private abbrev closedFree : FreeEnv D Γ := fun x => nomatch x
private abbrev closedBound : BoundEnv D .nil := fun i => Fin.elim0 i

private def emit (tag : Nat) : LetPar.Tm Empty Instr 0 := .op (.emit tag) .unit

private def emitD (tag : Nat) : Derivation Instr Γ .nil (emit tag) number :=
  .op .unit

/-- Both effects occur, and the tuple preserves the left and right result positions. -/
example :
    ((Derivation.par (emitD 2) (emitD 7)).denote D countInstr countPar
      (Control.seq D count) closedFree closedBound).run = (((2 : Nat), (7 : Nat)), 9) :=
  rfl

example :
    LetPar.Equiv false Γ .nil ((Tm.par (emit 2) (emit 7)).swap) (.par (emit 7) (emit 2))
      (product number number) :=
  Equiv.parSwap ⟨emitD 2⟩ ⟨emitD 7⟩

private def choose (left : Bool) : LetParCase.Tm Empty Instr 0 :=
  .case LetParCase.hasCase
    (if left then .inl LetParCase.hasCase .unit else .inr LetParCase.hasCase .unit)
    (.op (.emit 1) (.bv 0)) (.op (.emit 2) (.bv 0))

private def chooseD (left : Bool) : Derivation Instr Γ .nil (choose left) number :=
  .case (match left with | true => .inl .unit | false => .inr .unit) (.op .bv) (.op .bv)

private def runChoice (left : Bool) : (Nat × Nat) × Nat :=
  ((Derivation.par (chooseD left) (LetParCase.ofLetParDerivation (emitD 4))).denote D
    countInstr countPar (Control.case D count) closedFree closedBound).run

/-- For either tag, the selected arm and the independent sibling contribute their effects. -/
example : runChoice true = ((1, 4), 5) ∧ runChoice false = ((2, 4), 6) :=
  ⟨rfl, rfl⟩

example :
    LetParCase.Equiv false Γ .nil (.par (choose true) (LetParCase.ofLetPar (emit 4)))
      (.case LetParCase.hasCase (.inl LetParCase.hasCase .unit)
        (.par (.op (.emit 1) (.bv 0)) (LetParCase.ofLetPar (emit 4)).lift)
        (.par (.op (.emit 2) (.bv 0)) (LetParCase.ofLetPar (emit 4)).lift))
      (product number number) :=
  LetParCase.parCaseLeft (X := Ty.unit) (Y := Ty.unit) (.inl .unit) ⟨.inl .unit⟩ ⟨.op .bv⟩ ⟨.op .bv⟩
    ⟨LetParCase.ofLetParDerivation (emitD 4)⟩

private abbrev trace (α : Type) := Writer (List Nat) α

private def traceInstr : InstructionModel D Instr trace where
  eval
    | .emit tag, _ => WriterT.mk (tag, [tag])

private def leftFirst : ParOp trace := fun a b => do
  let x ← a
  let y ← b
  pure (x, y)

private def swapped : Derivation Instr Γ .nil ((Tm.par (emit 2) (emit 7)).swap)
    (product number number) :=
  .let₂ (.par (emitD 2) (emitD 7)) (.pair .bv .bv)

private def runTrace {t : LetPar.Tm Empty Instr 0} {A : Ty Unit}
    (d : Derivation Instr Γ .nil t A) : D A × List Nat :=
  (d.denote D traceInstr leftFirst (Control.seq D trace) closedFree closedBound).run

/-- Sequential replacement of Par fails the swap equation in an ordered effect model. -/
example : runTrace swapped ≠ runTrace (.par (emitD 7) (emitD 2)) := by
  change (((7, 2), [2, 7]) : (Nat × Nat) × List Nat) ≠ ((7, 2), [7, 2])
  decide

#print axioms Silmaril.Isotope.Parallel.Tm.widen_injective
#print axioms Silmaril.Isotope.Parallel.Equiv.parMap
#print axioms Silmaril.Isotope.LetPar.embed_injective
#print axioms Silmaril.Isotope.LetPar.embed_equiv
#print axioms Silmaril.Isotope.LetPar.denote_derivation
#print axioms Silmaril.Isotope.LetParCase.embed_injective
#print axioms Silmaril.Isotope.LetParCase.embed_equiv
#print axioms Silmaril.Isotope.LetParCase.denote_derivation
#print axioms Silmaril.Isotope.LetParCase.embed_seqCase

end LetParRegression

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.Semantics
open Silmaril.Elgot

namespace LetIterWeakTreeSoundness

inductive Prim where
  | next
  | unitMap
  | stop (label : Bool)

abbrev T := Ty Unit
abbrev atom : T := .base ()
abbrev Fx := Bool × Bool
abbrev bound : Fx := (true, false)

instance : HasTy Prim T :=
  ⟨fun | .next => atom | _ => unit,
   fun | .next => atom | .unitMap => unit | .stop _ => empty⟩
instance : HasEff Prim Fx := ⟨fun | .stop _ => bound | _ => ⊥⟩
instance : EffectIteration Fx := EffectIteration.complete Fx

def chain : Nat → Expr Prim
  | 0 => .var 0
  | n + 1 => .op .next (chain n)

abbrev Γ₁ : EffectCtx T Fx := [(atom, ⊥)]

theorem chain_typed (n : Nat) (e : Fx) : Wf Γ₁ (chain n) atom e := by
  induction n with
  | zero => exact .var (Γ := Γ₁) 0 bot_le
  | succ n ih => exact .op (f := Prim.next) bot_le ih

inductive Events : Type → Type
  | stop (label : Bool) : Events PEmpty

abbrev D (S : Type 1) := Ty.denote (fun _ : Unit => S)
abbrev free := (Ctx.nil : Ctx Empty T)
abbrev β₁ := Γ₁.toBoundCtx

noncomputable def treeInstr (S : Type 1) (step : S → S) :
    InstructionModel (D S) Prim (ITree.Tree Events) where
  eval
    | .next, x => ITree.ret (step x)
    | .unitMap, x => ITree.ret x
    | .stop b, _ => ITree.vis (.stop b) (fun x => x.elim)

theorem treeInstr_respectsPure (S : Type 1) (step : S → S) :
    InstructionModel.RespectsPure (ε := Fx) (treeInstr S step) := by
  intro f h
  cases f with
  | next => exact ⟨step, fun _ => rfl⟩
  | unitMap => exact ⟨id, fun _ => rfl⟩
  | stop b =>
    have hne : bound ≠ (⊥ : Fx) := by decide
    exact (hne h).elim

def observeHead {A X : Type 1} : ITree.Visible Events A X → Option Bool
  | .ret _ => none
  | .vis (.stop b) _ => some b

noncomputable def headLabel {A : Type 1} (t : ITree.Tree Events A) : _root_.Part (Option Bool) :=
  (ITree.out t).map observeHead

def nativeChain : Nat → Tm Empty Prim 1
  | 0 => .bv 0
  | n + 1 => .op .next (nativeChain n)

theorem chain_lowers (n : Nat) : (chain n).toLetIter 1 = some (nativeChain n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, nativeChain, Expr.toLetIter, ih]

def chainDeriv (n : Nat) : Derivation Prim free β₁ (nativeChain n) atom :=
  match n with
  | 0 => .bv (ι := 0)
  | n + 1 => .op (chainDeriv n)

def freeEnv (S : Type 1) : FreeEnv (D S) free := fun x => x.elim

def env₁ (S : Type 1) (x : S) : BoundEnv (D S) β₁ :=
  BoundEnv.snoc (β := .nil) (fun i => i.elim0) x

noncomputable def evalChain (S : Type 1) (step : S → S) (n : Nat) (x : S) :
    ITree.Tree Events S :=
  Derivation.denote (D S) (treeInstr S step) (chainDeriv n) (freeEnv S) (env₁ S x)

def applyN {S : Type 1} (step : S → S) : Nat → S → S
  | 0, x => x
  | n + 1, x => step (applyN step n x)

theorem evalChain_ret (S : Type 1) (step : S → S) (n : Nat) (x : S) :
    evalChain S step n x = ITree.ret (applyN step n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((evalChain S step n x) >>= (fun x => ITree.ret (step x))) =
      ITree.ret (step (applyN step n x))
    rw [ih]
    exact pure_bind _ _

abbrev N := ULift.{1} Nat
def nextNat (n : N) : N := ⟨n.down + 1⟩

theorem evalChain_N (n : Nat) : evalChain N nextNat n ⟨0⟩ = ITree.ret (⟨n⟩ : N) := by
  have h : applyN nextNat n ⟨0⟩ = (⟨n⟩ : N) := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg nextNat ih
  rw [evalChain_ret, h]

/-- The soundness step accepts any derivation, including one with native
iteration or an above-bound subterm in an intermediate expression. -/
theorem native_chain_eq_iff (n m : Nat) :
    AbortEquiv (⊥ : Fx) free β₁ (nativeChain n) (nativeChain m) atom ↔ n = m := by
  constructor
  · intro h
    have he : evalChain N nextNat n ⟨0⟩ = evalChain N nextNat m ⟨0⟩ :=
      denote_eq_of_abortEquiv_nil (fun _ : Unit => N) (treeInstr N nextNat)
        (treeInstr_respectsPure N nextNat) h (chainDeriv n) (chainDeriv m) (env₁ N ⟨0⟩)
    rw [evalChain_N, evalChain_N, ITree.ret_inj] at he
    exact congrArg ULift.down he
  · rintro rfl
    exact .equiv (.refl (chainDeriv n).toHasType)

/-- Endpoint conservativity on unary words at the source's original bound. -/
theorem unary_endpoint_conservativity (e : Fx) (n m : Nat) :
    AbortEquiv (⊥ : Fx) free β₁ (nativeChain n) (nativeChain m) atom ↔
      Eqv Γ₁ atom e (chain n) (chain m) := by
  constructor
  · intro h
    obtain rfl := (native_chain_eq_iff n m).mp h
    exact .refl (chain_typed n e)
  · intro h
    exact h.toLetIter (chain_lowers n) (chain_lowers m)

def unitProg : Expr Prim := .op .unitMap .unit
def unitDeriv : Derivation Prim free .nil (.unit : Tm Empty Prim 0) unit := .unit
def unitProgDeriv : Derivation Prim free .nil (.op .unitMap .unit : Tm Empty Prim 0) unit :=
  .op .unit

theorem terminality_without_events (S : Type 1) (step : S → S) :
    Eqv ([] : EffectCtx T Fx) unit (⊥ : Fx) unitProg .unit ∧
    Derivation.denoteClosed (D S) (treeInstr S step) unitProgDeriv =
      Derivation.denoteClosed (D S) (treeInstr S step) unitDeriv := by
  refine ⟨.step (.terminal (.op le_rfl (.unit _ _)) (.unit _ _)), ?_⟩
  simp only [Derivation.denoteClosed, unitProgDeriv, unitDeriv, Derivation.denote]
  erw [pure_bind]
  rfl

def abortLeft (b : Bool) : Expr Prim := .let₁ (.abort (.op (.stop b) .unit)) unitProg
def abortRight (b : Bool) : Expr Prim :=
  .let₁ (.op (.stop b) .unit) (.let₁ (.abort (.var 0)) unitProg)
def leftNative (b : Bool) : Tm Empty Prim 0 :=
  .let₁ (.abort (.op (.stop b) .unit)) (.op .unitMap .unit)
def rightNative (b : Bool) : Tm Empty Prim 0 :=
  .let₁ (.op (.stop b) .unit) (.let₁ (.abort (.bv 0)) (.op .unitMap .unit))

def leftTyped (b : Bool) : TypedExpr Prim ([] : EffectCtx T Fx) unit bound :=
  ⟨abortLeft b, .let₁ (A := unit) (.abort (.op le_rfl (.unit _ _))) (.op bot_le (.unit _ _))⟩
def rightTyped (b : Bool) : TypedExpr Prim ([] : EffectCtx T Fx) unit bound :=
  ⟨abortRight b, .let₁ (.op le_rfl (.unit _ _))
    (.let₁ (A := unit) (.abort (.var 0 bot_le)) (.op bot_le (.unit _ _)))⟩
def leftDeriv (b : Bool) : Derivation Prim free .nil (leftNative b) unit :=
  .let₁ (A := unit) (.abort (.op .unit)) (.op .unit)
def rightDeriv (b : Bool) : Derivation Prim free .nil (rightNative b) unit :=
  .let₁ (.op .unit) (.let₁ (A := unit) (.abort (.bv (ι := 0))) (.op .unit))

theorem observe_stop_bind (S : Type 1) (b : Bool)
    (k : D S empty → ITree.Tree Events (D S unit)) :
    headLabel (ITree.vis (.stop b) (fun x : PEmpty => x.elim) >>= k) =
      .some (some b) := by
  rw [ITree.vis_bind]
  simp [headLabel, observeHead]

theorem strict_bound_abort (S : Type 1) (step : S → S) (b : Bool) :
    (⊥ : Fx) < bound ∧ bound < ⊤ ∧
    Eqv ([] : EffectCtx T Fx) unit bound (abortLeft b) (abortRight b) ∧
    HasTypeEffect free .nil (leftNative b) unit bound ∧
    HasTypeEffect free .nil (rightNative b) unit bound ∧
    Derivation.denoteClosed (D S) (treeInstr S step) (leftDeriv b) =
      Derivation.denoteClosed (D S) (treeInstr S step) (rightDeriv b) ∧
    headLabel (Derivation.denoteClosed (D S) (treeInstr S step) (rightDeriv b)) =
      .some (some b) := by
  have h : Eqv ([] : EffectCtx T Fx) unit bound (abortLeft b) (abortRight b) :=
    .step (.rewrite (leftTyped b).prop (rightTyped b).prop (.let1_abort _ _))
  obtain ⟨ht, hs, he⟩ := Eqv.toLetIter_at_bound (leftTyped b) (rightTyped b) h rfl rfl
  refine ⟨lt_of_le_of_ne bot_le (by decide), lt_of_le_of_ne le_top (by decide), h, ht, hs, ?_, ?_⟩
  · exact denote_eq_of_abortEquiv_nil (fun _ : Unit => S) (treeInstr S step)
      (treeInstr_respectsPure S step) he (leftDeriv b) (rightDeriv b) (fun i => i.elim0)
  · change headLabel (((pure (PUnit.unit : D S unit) : ITree.Tree Events _) >>=
      (fun _ => ITree.vis (.stop b) (fun x : PEmpty => x.elim : PEmpty → ITree.Tree Events (D S empty))))
      >>= _) = _
    rw [pure_bind]
    exact observe_stop_bind S b _

end LetIterWeakTreeSoundness

namespace LetIterResponseSingleCall

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

inductive Prim where
  | next
  | read
  | readOther
  | readAlt
  | join

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev T := Ty Bool
abbrev inputSort : T := .base false
abbrev outputSort : T := .base true

/-- The reads include two operations at the same type and one at the opposite
type. The pure join takes two ordered arguments. -/
abbrev sig : Signature Bool Prim :=
  ⟨fun | .join => 2 | _ => 1,
    fun f _ => match f with | .readOther | .join => true | _ => false,
    fun | .read | .readAlt | .join => true | _ => false⟩

local instance : HasTy Prim T := sig.endpoints
local instance : HasEff Prim Fx := ⟨fun | .next | .join => ⊥ | _ => strict⟩
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev Γ : EffectCtx T Fx := [(outputSort, ⊥), (inputSort, ⊥)]
abbrev sorts : Fin Γ.length → Bool := Fin.cases true (fun _ => false)
abbrev Γ' : EffectCtx T Fx := (outputSort, ⊥) :: Γ
abbrev sorts' : Fin Γ'.length → Bool := Fin.cases true sorts
abbrev Γ₀ := (Ctx.nil : Ctx Empty T)

theorem ctx_pure : Γ.Pure := by
  unfold EffectCtx.Pure
  decide

theorem slots_typed : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (sorts i) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  rw [Fin.eq_zero j]
  rfl

theorem extended_slots_typed : ∀ i : Fin Γ'.length, (Γ'.get i).1 = .base (sorts' i) :=
  fun i => Fin.cases (motive := fun j => (Γ'.get j).1 = .base (sorts' j)) rfl slots_typed i

abbrev args : (i : Fin (sig.arity Prim.read)) → Tree sig sorts (sig.arg Prim.read i) :=
  fun _ => .op Prim.next (fun _ => .var 1)

theorem args_pure : ∀ i, DeclaredPure (ε := Fx) sig (args i) :=
  fun _ => ⟨rfl, fun _ => trivial⟩

theorem read_not_pure : ¬ IsPure (⊥ : Fx) Prim.read := by
  change strict ≠ (⊥ : Fx)
  decide

theorem strict_bound : (⊥ : Fx) < strict ∧ strict < ⊤ :=
  ⟨lt_of_le_of_ne bot_le (by decide), lt_of_le_of_ne le_top (by decide)⟩

abbrev request : Tree sig sorts true := .op Prim.read args
abbrev receive : Expr Prim := .var 0
abbrev ignoreResponse : Expr Prim := .var 1
abbrev receiveThroughLet : Expr Prim := .let₁ (.var 0) (.var 0)

theorem receive_wf : Wf Γ' receive outputSort (⊥ : Fx) := .var 0 le_rfl
theorem ignore_wf : Wf Γ' ignoreResponse outputSort (⊥ : Fx) := .var 1 le_rfl
theorem receive_let_wf : Wf Γ' receiveThroughLet outputSort (⊥ : Fx) :=
  .let₁ receive_wf (.var 0 le_rfl)

/-- The same normalized request distinguishes returning its response from
returning the existing variable of the same result sort. -/
theorem response_differs_from_ambient :
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (.let₁ request.native (.bv 0))
      (.let₁ request.native (.bv 1)) outputSort := by
  intro h
  have he := Response.SingleCall.continuation_eqv sig ctx_pure slots_typed args args_pure
    read_not_pure strict le_rfl receive_wf ignore_wf (t := .bv 0) (s := .bv 1) rfl rfl h
  let x : Tree sig sorts' true := .var 0
  let y : Tree sig sorts' true := .var 1
  have hΓ' : Γ'.Pure := by unfold EffectCtx.Pure; decide
  have eqTrees := (source_eqv_iff sig x y trivial trivial hΓ' extended_slots_typed strict).mp he
  let index {a : Bool} (z : Tree sig sorts' a) : Option Nat := match z with
    | .var i => some i.val
    | .op _ _ => none
  exact (by decide : (some 0 : Option Nat) ≠ some 1) (congrArg index eqTrees)

theorem response_differs_from_ambient_at_bound :
    ¬ Eqv Γ outputSort strict (.let₁ request.source receive)
      (.let₁ request.source ignoreResponse) := by
  intro h
  exact response_differs_from_ambient (h.toLetIter rfl rfl)

/-- A let in the continuation is normalized automatically at the original bound. -/
theorem let_in_continuation :
    AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (.let₁ request.native (.let₁ (.bv 0) (.bv 0)))
      (.let₁ request.native (.bv 0)) outputSort ↔
    Eqv Γ outputSort strict (.let₁ request.source receiveThroughLet)
      (.let₁ request.source receive) :=
  Response.SingleCall.endpoint_reflection sig ctx_pure slots_typed args args_pure
    read_not_pure strict le_rfl receive_let_wf receive_wf rfl rfl

example : Eqv Γ outputSort strict (.let₁ request.source receiveThroughLet)
    (.let₁ request.source receive) := by
  have ht : Wf Γ request.source outputSort strict :=
    .op (f := Prim.read) le_rfl
      (.pair (.op (f := Prim.next) bot_le (.pair (.var 1 bot_le) (.unit _ _))) (.unit _ _))
  obtain ⟨t, hl, htyped⟩ := ht.toLetIter
  have he : t = request.native := Option.some.inj (hl.symm.trans rfl)
  subst t
  exact let_in_continuation.mp (.equiv (.let₁ (.refl htyped.1) (Equiv.letEta .bv)))

theorem read_other_not_pure : ¬ IsPure (⊥ : Fx) Prim.readOther := by
  change strict ≠ (⊥ : Fx)
  decide

abbrev otherArgs : Response.Args sig sorts Prim.readOther := fun _ => .var 0

/-- The request equality resolves the primitive before comparing its dependent
argument tuple, even when the response sorts differ. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (.let₁ request.native (.bv 0))
    (.let₁ (Tree.op Prim.readOther otherArgs).native (.bv 1)) outputSort := by
  intro hn
  have h := Response.SingleCall.request_eq sig slots_typed args otherArgs
    args_pure (fun _ => trivial) read_not_pure read_other_not_pure hn
  have hfg : Prim.read = Prim.readOther := congrArg Sigma.fst h
  cases hfg

abbrev normArg : Expr Prim := sourceTuple 1 (fun i => (args i).source)
abbrev normArgNative : Tm Empty Prim Γ.length := nativeTuple 1 (fun i => (args i).native)
abbrev rawArg : Expr Prim := .let₁ normArg (.var 0)
abbrev rawArgNative : Tm Empty Prim Γ.length := .let₁ normArgNative (.bv 0)

theorem arg_wf : Wf Γ normArg (input (sig.arity Prim.read) (sig.arg Prim.read)) (⊥ : Fx) :=
  .pair (.op (f := Prim.next) le_rfl (.pair (.var 1 le_rfl) (.unit _ _))) (.unit _ _)

example : Eqv Γ outputSort strict (.let₁ (.op Prim.read rawArg) receive)
    (.let₁ (.op Prim.read normArg) receive) := by
  have hreflect := Response.SingleCall.endpoint_reflection_pure_arguments sig ctx_pure slots_typed
    read_not_pure read_not_pure strict le_rfl le_rfl
    (x := rawArg) (y := normArg) (.let₁ arg_wf (.var 0 le_rfl)) arg_wf receive_wf receive_wf
    (x₀ := rawArgNative) (y₀ := normArgNative) (t := .bv 0) (s := .bv 0) rfl rfl rfl rfl
  obtain ⟨arg, hl, ht⟩ := arg_wf.toLetIter
  have he : arg = normArgNative := Option.some.inj (hl.symm.trans rfl)
  subst arg
  exact hreflect.mp (.equiv (.let₁ (.op (Equiv.letEta ht.1)) (.refl .bv)))

abbrev useFirstResponse : Response.Sequence sig true sorts :=
  .call Prim.read args (.call Prim.readOther (fun _ => .var 0) (.ret (.var 1)))

abbrev useAmbientAtSecondCall : Response.Sequence sig true sorts :=
  .call Prim.read args (.call Prim.readOther (fun _ => .var 1) (.ret (.var 1)))

abbrev returnAmbientAfterTwoCalls : Response.Sequence sig true sorts :=
  .call Prim.read args (.call Prim.readOther (fun _ => .var 0) (.ret (.var 2)))

theorem firstResponse_wf : Response.Sequence.WellTyped sig strict useFirstResponse :=
  ⟨args_pure, read_not_pure, le_rfl, fun _ => trivial, read_other_not_pure, le_rfl, trivial⟩

theorem ambientAtSecondCall_wf : Response.Sequence.WellTyped sig strict useAmbientAtSecondCall :=
  ⟨args_pure, read_not_pure, le_rfl, fun _ => trivial, read_other_not_pure, le_rfl, trivial⟩

theorem ambientAfterTwoCalls_wf : Response.Sequence.WellTyped sig strict returnAmbientAfterTwoCalls :=
  ⟨args_pure, read_not_pure, le_rfl, fun _ => trivial, read_other_not_pure, le_rfl, trivial⟩

/-- The first response and a same-sort ambient variable give distinguishable
requests at the second call. -/
example : ¬ Eqv Γ outputSort strict useFirstResponse.source useAmbientAtSecondCall.source := by
  intro h
  have hn := (Response.Sequence.endpoint_reflection sig ctx_pure slots_typed strict
    useFirstResponse useAmbientAtSecondCall firstResponse_wf ambientAtSecondCall_wf).mpr h
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict
    useFirstResponse useAmbientAtSecondCall firstResponse_wf ambientAtSecondCall_wf hn
  let secondArgument : Expr Prim → Option Nat
    | .let₁ _ (.let₁ (.op _ (.pair (.var i) .unit)) _) => some i
    | _ => none
  have hi := congrArg (fun p => secondArgument (Response.Sequence.source sig p)) he
  exact (by decide : (some 0 : Option Nat) ≠ some 1) hi

/-- After the second call, the first response is at index one and the
original same-sort ambient variable is at index two. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    useFirstResponse.native returnAmbientAfterTwoCalls.native outputSort := by
  intro hn
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict
    useFirstResponse returnAmbientAfterTwoCalls firstResponse_wf ambientAfterTwoCalls_wf hn
  let finalVariable : Expr Prim → Option Nat
    | .let₁ _ (.let₁ _ (.var i)) => some i
    | _ => none
  have hi := congrArg (fun p => finalVariable (Response.Sequence.source sig p)) he
  exact (by decide : (some 1 : Option Nat) ≠ some 2) hi

example : useFirstResponse.source.toLetIter Γ.length =
    some (.let₁ request.native (.let₁ (.op Prim.readOther (.pair (.bv 0) .unit)) (.bv 1))) :=
  Response.Sequence.lowers sig useFirstResponse

abbrev returnAfterFirstCall : Response.Sequence sig true sorts :=
  .call Prim.read args (.ret (.var 0))

/-- A pure return is observable where the longer sequence makes its second call. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    returnAfterFirstCall.native useFirstResponse.native outputSort := by
  intro hn
  have hshort : Response.Sequence.WellTyped sig strict returnAfterFirstCall :=
    ⟨args_pure, read_not_pure, le_rfl, trivial⟩
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict
    returnAfterFirstCall useFirstResponse hshort firstResponse_wf hn
  let continuationCalls : Expr Prim → Bool
    | .let₁ _ (.let₁ _ _) => true
    | _ => false
  have h := congrArg (fun p => continuationCalls (Response.Sequence.source sig p)) he
  exact (by decide : false ≠ true) h

open Response.Flatten

abbrev pureOperand : Tree sig sorts false := .op Prim.next (fun _ => .var 1)
abbrev rawLeft : Program sig sorts true :=
  .let1 (.tree pureOperand) (.unary Prim.read rfl (.tree (.var 0)))
abbrev rawRight : Program sig sorts true :=
  .unary Prim.readAlt rfl (.tree (.var 1))

abbrev leftFirst : Program sig sorts true :=
  .binary Prim.join rfl rawLeft rawRight
abbrev rightFirst : Program sig sorts true :=
  .binary Prim.join rfl rawRight rawLeft

theorem typedLeft : Program.WellTyped sig strict rawLeft :=
  ⟨⟨rfl, fun _ => trivial⟩, le_rfl, trivial⟩

theorem typedRight : Program.WellTyped sig strict rawRight := ⟨le_rfl, trivial⟩

theorem typedLeftFirst : Program.WellTyped sig strict leftFirst :=
  ⟨bot_le, typedLeft, typedRight⟩
theorem typedRightFirst : Program.WellTyped sig strict rightFirst :=
  ⟨bot_le, typedRight, typedLeft⟩

noncomputable abbrev leftCode := compile (ε := Fx) sig leftFirst
noncomputable abbrev rightCode := compile (ε := Fx) sig rightFirst

def firstInstruction (p : Response.Sequence sig true sorts) : Option Prim :=
  match p with
  | .ret _ => none
  | .call f _ _ => some f

theorem read_alt_not_pure : ¬ IsPure (⊥ : Fx) Prim.readAlt := by
  change strict ≠ (⊥ : Fx)
  decide

theorem leftHead : firstInstruction leftCode = some Prim.read := by
  simp only [leftCode, compile, unaryTail, emit,
    ite_eq_right read_not_pure, Response.Sequence.bind, Response.Sequence.subst, firstInstruction]

theorem rightHead : firstInstruction rightCode = some Prim.readAlt := by
  simp only [rightCode, compile, unaryTail, emit,
    ite_eq_right read_alt_not_pure, Response.Sequence.bind, Response.Sequence.subst, firstInstruction]

def visibleOrder : {n : Nat} → {ts : Fin n → Bool} → {c : Bool} →
    Response.Sequence sig c ts → List Prim
  | _, _, _, .ret _ => []
  | _, _, _, .call f _ rest => f :: visibleOrder rest

theorem join_pure : IsPure (⊥ : Fx) Prim.join := rfl

example : visibleOrder leftCode = [Prim.read, Prim.readAlt] := by
  simp only [leftCode, compile, unaryTail, binaryTail, emit,
    ite_eq_right read_not_pure, ite_eq_right read_alt_not_pure, ite_eq_left join_pure,
    Response.Sequence.bind, Response.Sequence.weaken, Response.Sequence.subst, visibleOrder]

/-- An effectful unary argument finishes its own call before the outer call. -/
example : visibleOrder (compile (ε := Fx) sig (.unary Prim.readOther rfl rawLeft)) =
    [Prim.read, Prim.readOther] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_not_pure,
    ite_eq_right read_other_not_pure, Response.Sequence.bind, Response.Sequence.subst, visibleOrder]

/-- Swapping the effectful operands changes the head even though the final
binary primitive is pure. The left operand starts with a pure let. -/
theorem swapped_arguments_source_ne :
    ¬ Eqv Γ outputSort strict leftFirst.source rightFirst.source := by
  intro h
  have hl := compile_eqv sig ctx_pure slots_typed strict leftFirst typedLeftFirst
  have hr := compile_eqv sig ctx_pure slots_typed strict rightFirst typedRightFirst
  have hseq := hl.symm.trans (h.trans hr)
  have hn := hseq.toLetIter (Response.Sequence.lowers sig leftCode) (Response.Sequence.lowers sig rightCode)
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict leftCode rightCode
    (compile_typed sig strict leftFirst typedLeftFirst)
    (compile_typed sig strict rightFirst typedRightFirst) hn
  have hhead := leftHead.symm.trans ((congrArg firstInstruction he).trans rightHead)
  cases hhead

/-- The lowered raw programs are separated even when the native proof can use
all well-typed intermediate terms. -/
theorem swapped_arguments_native_ne {t s : Tm Empty Prim Γ.length}
    (ht : leftFirst.source.toLetIter Γ.length = some t)
    (hs : rightFirst.source.toLetIter Γ.length = some s) :
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort := by
  intro hn
  exact swapped_arguments_source_ne
    ((endpoint_reflection sig ctx_pure slots_typed strict leftFirst rightFirst
      typedLeftFirst typedRightFirst ht hs).mp hn)

example : ∃ t s : Tm Empty Prim Γ.length,
    leftFirst.source.toLetIter Γ.length = some t ∧
    rightFirst.source.toLetIter Γ.length = some s ∧
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort := by
  obtain ⟨t, ht, _⟩ := (source_wf sig ctx_pure slots_typed strict leftFirst typedLeftFirst).toLetIter
  obtain ⟨s, hs, _⟩ := (source_wf sig ctx_pure slots_typed strict rightFirst typedRightFirst).toLetIter
  exact ⟨t, s, ht, hs, swapped_arguments_native_ne ht hs⟩

section EffectfulCase

abbrev Γsum : EffectCtx T Fx := (Ty.coprod inputSort outputSort, ⊥) :: Γ
abbrev Γleft : EffectCtx T Fx := (inputSort, ⊥) :: Γ
abbrev Γright : EffectCtx T Fx := (outputSort, ⊥) :: Γ
abbrev leftSlots : Fin Γleft.length → Bool := Response.extendSorts false sorts
abbrev rightSlots : Fin Γright.length → Bool := Response.extendSorts true sorts

abbrev leftArm : Program sig leftSlots true :=
  .unary Prim.read rfl (.tree (.var 0))
abbrev changedLeft : Program sig leftSlots true :=
  .unary Prim.readAlt rfl (.tree (.var 0))

/-- The right arm uses its own payload to issue a request at a different type.
Its response becomes the argument of the next request. -/
abbrev rightArm : Program sig rightSlots true :=
  .let1 (.unary Prim.readOther rfl (.tree (.var 0)))
    (.unary Prim.readAlt rfl (.tree (.var 0)))
abbrev changedRight : Program sig rightSlots true :=
  .unary Prim.readAlt rfl (.tree (.var 2))

private theorem leftArm_typed : Program.WellTyped sig strict leftArm := ⟨le_rfl, trivial⟩
private theorem changedLeft_typed : Program.WellTyped sig strict changedLeft := ⟨le_rfl, trivial⟩
private theorem rightArm_typed : Program.WellTyped sig strict rightArm :=
  ⟨⟨le_rfl, trivial⟩, le_rfl, trivial⟩
private theorem changedRight_typed : Program.WellTyped sig strict changedRight := ⟨le_rfl, trivial⟩

private theorem branchSlots {a : Bool} :
    ∀ i : Fin ((Ty.base a, (⊥ : Fx)) :: Γ).length,
      (((Ty.base a, (⊥ : Fx)) :: Γ).get i).1 = .base (Response.extendSorts a sorts i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base a, (⊥ : Fx)) :: Γ).get j).1 = .base (Response.extendSorts a sorts j))
    rfl slots_typed i

private theorem branchPure (a : Bool) : EffectCtx.Pure ((Ty.base a, (⊥ : Fx)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((Ty.base a, (⊥ : Fx)) :: Γ).get j).2 = ⊥)
    rfl ctx_pure i

private theorem caseWf (l : Program sig leftSlots true) (r : Program sig rightSlots true)
    (hl : Program.WellTyped sig strict l) (hr : Program.WellTyped sig strict r) :
    Wf Γsum (Response.Case.onHead l.source r.source) outputSort strict :=
  Response.Case.source_wf
    (source_wf sig (branchPure false) branchSlots strict l hl)
    (source_wf sig (branchPure true) branchSlots strict r hr)

private theorem unequalOrders {Δ : EffectCtx T Fx} {ss : Fin Δ.length → Bool}
    (hΔ : Δ.Pure) (hs : ∀ i, (Δ.get i).1 = .base (ss i))
    (p q : Program sig ss true) (hp : Program.WellTyped sig strict p)
    (hq : Program.WellTyped sig strict q)
    (h : visibleOrder (compile (ε := Fx) sig p) ≠ visibleOrder (compile (ε := Fx) sig q)) :
    ¬ Eqv Δ outputSort strict p.source q.source := by
  intro he
  have ep := compile_eqv sig hΔ hs strict p hp
  have eq := compile_eqv sig hΔ hs strict q hq
  have hn := (ep.symm.trans (he.trans eq)).toLetIter
    (Response.Sequence.lowers sig (compile (ε := Fx) sig p))
    (Response.Sequence.lowers sig (compile (ε := Fx) sig q))
  exact h (congrArg visibleOrder (Response.Sequence.native_eq_implies_eq sig hs strict _ _
    (compile_typed sig strict p hp) (compile_typed sig strict q hq) hn))

private theorem leftOrder :
    visibleOrder (compile (ε := Fx) sig leftArm) = [Prim.read] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_not_pure, Response.Sequence.bind,
    Response.Sequence.subst, visibleOrder]

private theorem changedLeftOrder :
    visibleOrder (compile (ε := Fx) sig changedLeft) = [Prim.readAlt] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_alt_not_pure, Response.Sequence.bind,
    Response.Sequence.subst, visibleOrder]

private theorem rightOrder :
    visibleOrder (compile (ε := Fx) sig rightArm) = [Prim.readOther, Prim.readAlt] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_other_not_pure,
    ite_eq_right read_alt_not_pure, Response.Sequence.bind, Response.Sequence.subst, visibleOrder]

private theorem changedRightOrder :
    visibleOrder (compile (ε := Fx) sig changedRight) = [Prim.readAlt] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_alt_not_pure, Response.Sequence.bind,
    Response.Sequence.subst, visibleOrder]

/-- Changing either arm is visible, even though the other arm and scrutinee are
identical. The three raw cases lower at the original strict bound. -/
theorem effectful_case_observes_both_tags :
    ∃ t l r : Tm Empty Prim Γsum.length,
      (Response.Case.onHead leftArm.source rightArm.source).toLetIter Γsum.length = some t ∧
      (Response.Case.onHead changedLeft.source rightArm.source).toLetIter Γsum.length = some l ∧
      (Response.Case.onHead leftArm.source changedRight.source).toLetIter Γsum.length = some r ∧
      ¬ AbortEquiv (⊥ : Fx) Γ₀ Γsum.toBoundCtx t l outputSort ∧
      ¬ AbortEquiv (⊥ : Fx) Γ₀ Γsum.toBoundCtx t r outputSort := by
  obtain ⟨t, ht, _⟩ := (caseWf leftArm rightArm leftArm_typed rightArm_typed).toLetIter
  obtain ⟨l, hl, _⟩ := (caseWf changedLeft rightArm changedLeft_typed rightArm_typed).toLetIter
  obtain ⟨r, hr, _⟩ := (caseWf leftArm changedRight leftArm_typed changedRight_typed).toLetIter
  refine ⟨t, l, r, ht, hl, hr, ?_, ?_⟩
  · intro hn
    have he := Response.Case.arms_eqv_of_native sig ctx_pure slots_typed strict
      leftArm changedLeft rightArm rightArm
      leftArm_typed changedLeft_typed rightArm_typed rightArm_typed ht hl hn
    exact unequalOrders (branchPure false) branchSlots leftArm changedLeft leftArm_typed
      changedLeft_typed (by rw [leftOrder, changedLeftOrder]; intro h; cases h) he.1
  · intro hn
    have he := (Response.Case.endpoint_reflection sig ctx_pure slots_typed strict
      leftArm leftArm rightArm changedRight leftArm_typed leftArm_typed
      rightArm_typed changedRight_typed ht hr).mp hn
    have harms := (Response.Case.eqv_iff_arms
      (source_wf sig (branchPure false) branchSlots strict leftArm leftArm_typed)
      (source_wf sig (branchPure true) branchSlots strict rightArm rightArm_typed)
      (source_wf sig (branchPure false) branchSlots strict leftArm leftArm_typed)
      (source_wf sig (branchPure true) branchSlots strict changedRight changedRight_typed)).mp he
    exact unequalOrders (branchPure true) branchSlots rightArm changedRight rightArm_typed
      changedRight_typed (by rw [rightOrder, changedRightOrder]; intro h; cases h) harms.2

end EffectfulCase

section EffectfulDecisionTree

open Response.DecisionTree (Shape)

abbrev Γdec : EffectCtx T Fx :=
  [(Ty.coprod inputSort outputSort, ⊥), (outputSort, ⊥), (Ty.coprod inputSort inputSort, ⊥)]
abbrev firstSplit : Fin Γdec.length := 0
abbrev Γfirst (x : Bool) := SumSplit.branchCtx Γdec firstSplit (.base x)
abbrev secondSplit (x : Bool) : Fin (Γfirst x).length := ⟨2, by change 2 < 3; decide⟩
abbrev Γleaf (x : Bool) := SumSplit.branchCtx (Γfirst x) (secondSplit x) inputSort

abbrev decisionSlots (x : Bool) : Fin (Γleaf x).length → Bool :=
  fun i => if i.val = 0 then x else if i.val = 1 then true else false

private theorem leafSlots_typed (x : Bool) :
    ∀ i : Fin (Γleaf x).length, ((Γleaf x).get i).1 = .base (decisionSlots x i) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  rw [Fin.eq_zero k]
  rfl

abbrev finalShape (x : Bool) : Shape (Γleaf x) :=
  .leaf (decisionSlots x) (leafSlots_typed x)
abbrev laterShape (x : Bool) : Shape (Γfirst x) :=
  .split (secondSplit x) (x := false) (y := false) rfl (finalShape x) (finalShape x)
abbrev fullShape : Shape Γdec :=
  .split firstSplit (x := false) (y := true) rfl (laterShape false) (laterShape true)

abbrev probeEarlier : Response.Flatten.Program sig (decisionSlots false) true :=
  .request Prim.read (fun _ => Tree.var (S := sig) (sorts := decisionSlots false)
    ⟨0, by change 0 < 3; decide⟩)
abbrev probeLater (x : Bool) : Response.Flatten.Program sig (decisionSlots x) true :=
  .request Prim.read (fun _ => Tree.var (S := sig) (sorts := decisionSlots x)
    ⟨2, by change 2 < 3; decide⟩)
abbrev leftTree (p : Response.Flatten.Program sig (decisionSlots false) true) :
    Response.DecisionTree.Program sig true (laterShape false) :=
  .split (secondSplit false) (.leaf p) (.leaf (probeLater false))
abbrev rightTree : Response.DecisionTree.Program sig true (laterShape true) :=
  .split (secondSplit true) (.leaf (probeLater true)) (.leaf (probeLater true))
abbrev decision (p : Response.Flatten.Program sig (decisionSlots false) true) :
    Response.DecisionTree.Program sig true fullShape :=
  .split firstSplit (leftTree p) rightTree

private theorem pureDecisionCtx : Γdec.Pure := by unfold EffectCtx.Pure; decide
private theorem earlier_typed : Response.Flatten.Program.WellTyped sig strict probeEarlier :=
  ⟨le_rfl, fun _ => trivial⟩
private theorem later_typed (x : Bool) : Response.Flatten.Program.WellTyped sig strict (probeLater x) :=
  ⟨le_rfl, fun _ => trivial⟩
private theorem leftTree_typed (p : Response.Flatten.Program sig (decisionSlots false) true)
    (hp : Response.Flatten.Program.WellTyped sig strict p) :
    Response.DecisionTree.Program.WellTyped sig strict (leftTree p) :=
  ⟨hp, later_typed false⟩
private theorem rightTree_typed : Response.DecisionTree.Program.WellTyped sig strict rightTree :=
  ⟨later_typed true, later_typed true⟩
private theorem decision_typed (p : Response.Flatten.Program sig (decisionSlots false) true)
    (hp : Response.Flatten.Program.WellTyped sig strict p) :
    Response.DecisionTree.Program.WellTyped sig strict (decision p) :=
  ⟨leftTree_typed p hp, rightTree_typed⟩

private def nestedRequestIndex : Expr Prim → Option Nat
  | .case (.var 0) (.case (.var 3) (.op .read (.pair (.var i) .unit)) _) _ => some i
  | _ => none

-- At the second test, the first payload is the older of the two binders.
example : nestedRequestIndex (decision probeEarlier).source = some 1 := rfl
example : nestedRequestIndex (decision (probeLater false)).source = some 0 := rfl

private theorem leafRequestsDiffer :
    ¬ Eqv (Γleaf false) outputSort strict probeEarlier.source (probeLater false).source := by
  intro he
  have hpure : (Γleaf false).Pure := by unfold EffectCtx.Pure; decide
  let p := compile (ε := Fx) sig probeEarlier
  let q := compile (ε := Fx) sig (probeLater false)
  have ep := compile_eqv sig hpure (leafSlots_typed false) strict probeEarlier earlier_typed
  have eq := compile_eqv sig hpure (leafSlots_typed false) strict (probeLater false) (later_typed false)
  have hn := (ep.symm.trans (he.trans eq)).toLetIter
    (Response.Sequence.lowers sig p) (Response.Sequence.lowers sig q)
  have h := Response.Sequence.native_eq_implies_eq sig (leafSlots_typed false) strict p q
    (compile_typed sig strict probeEarlier earlier_typed)
    (compile_typed sig strict (probeLater false) (later_typed false)) hn
  let argumentIndex : Expr Prim → Option Nat
    | .let₁ (.op .read (.pair (.var i) .unit)) _ => some i
    | _ => none
  have h0 : argumentIndex p.source = some 0 := by
    simp only [p, compile, emit, ite_eq_right read_not_pure, Response.Sequence.source,
      Tree.source, sourceTuple, argumentIndex]
  have h2 : argumentIndex q.source = some 2 := by
    simp only [q, compile, emit, ite_eq_right read_not_pure, Response.Sequence.source,
      Tree.source, sourceTuple, argumentIndex]
  exact (by decide : (some 0 : Option Nat) ≠ some 2)
    (h0.symm.trans ((congrArg (fun p => argumentIndex (Response.Sequence.source sig p)) h).trans h2))

private theorem decisionSourceDiffers :
    ¬ Eqv Γdec outputSort strict (decision probeEarlier).source
      (decision (probeLater false)).source := by
  intro h
  have hL : (Γfirst false).Pure := SumSplit.branchCtx_pure pureDecisionCtx firstSplit inputSort
  have hR : (Γfirst true).Pure := SumSplit.branchCtx_pure pureDecisionCtx firstSplit outputSort
  have hr := Response.DecisionTree.source_wf sig hR strict rightTree rightTree_typed
  have hl := Response.DecisionTree.source_wf sig hL strict (leftTree probeEarlier)
    (leftTree_typed probeEarlier earlier_typed)
  have hl' := Response.DecisionTree.source_wf sig hL strict (leftTree (probeLater false))
    (leftTree_typed (probeLater false) (later_typed false))
  have hleft := (SumSplit.caseArms_eqv_iff firstSplit rfl rfl hl hr hl' hr).mp h
  have hpure : (Γleaf false).Pure :=
    SumSplit.branchCtx_pure hL (secondSplit false) inputSort
  have he := source_wf sig hpure (leafSlots_typed false) strict probeEarlier earlier_typed
  have ha := source_wf sig hpure (leafSlots_typed false) strict (probeLater false) (later_typed false)
  exact leafRequestsDiffer ((SumSplit.caseArms_eqv_iff (secondSplit false) rfl rfl he ha ha ha).mp
    hleft.1).1

/-- The same nested request uses either the earlier payload or the second
payload. A native equality cannot identify those inputs. -/
theorem nested_case_distinguishes_payloads :
    ∃ t s : Tm Empty Prim Γdec.length,
      (decision probeEarlier).source.toLetIter Γdec.length = some t ∧
      (decision (probeLater false)).source.toLetIter Γdec.length = some s ∧
      ¬ AbortEquiv (⊥ : Fx) Γ₀ Γdec.toBoundCtx t s outputSort := by
  let p := decision probeEarlier
  let q := decision (probeLater false)
  have hp := decision_typed probeEarlier earlier_typed
  have hq := decision_typed (probeLater false) (later_typed false)
  obtain ⟨t, ht, _⟩ := (Response.DecisionTree.source_wf sig pureDecisionCtx strict p hp).toLetIter
  obtain ⟨s, hs, _⟩ := (Response.DecisionTree.source_wf sig pureDecisionCtx strict q hq).toLetIter
  exact ⟨t, s, ht, hs, fun h => decisionSourceDiffers
    ((Response.DecisionTree.endpoint_reflection sig pureDecisionCtx strict p q hp hq ht hs).mp h)⟩

end EffectfulDecisionTree

section ReorderedDecisionTree

open Response.DecisionTree (Shape Program)

abbrev Γmix : EffectCtx T Fx :=
  [(Ty.coprod inputSort inputSort, ⊥), (outputSort, ⊥), (Ty.coprod inputSort inputSort, ⊥)]
abbrev Γhead := SumSplit.branchCtx Γmix 0 inputSort
abbrev Γtail := SumSplit.branchCtx Γmix 2 inputSort

abbrev headNext : Fin Γhead.length := ⟨2, by decide⟩
abbrev tailNext : Fin Γtail.length := ⟨0, by decide⟩
abbrev headArm : Shape Γhead := .split headNext rfl (finalShape false) (finalShape false)
abbrev tailArm : Shape Γtail := .split tailNext rfl (finalShape false) (finalShape false)
abbrev headFirst : Shape Γmix := .split 0 rfl headArm headArm
abbrev tailFirst : Shape Γmix := .split 2 rfl tailArm tailArm

abbrev twice (rev : Bool) : Response.Flatten.Program sig (decisionSlots false) true :=
  if rev then
    .let1 (probeLater false) (.request Prim.read (fun _ =>
      Tree.var (S := sig) (sorts := Response.extendSorts true (decisionSlots false)) 1))
  else
    .let1 probeEarlier (.request Prim.read (fun _ =>
      Tree.var (S := sig) (sorts := Response.extendSorts true (decisionSlots false)) 3))

private theorem twice_typed (rev : Bool) : Response.Flatten.Program.WellTyped sig strict (twice rev) := by
  cases rev <;> exact ⟨⟨le_rfl, fun _ => trivial⟩, ⟨le_rfl, fun _ => trivial⟩⟩

abbrev headProgram (a : Bool) : Program sig true headArm :=
  .split headNext (.leaf (twice a)) (.leaf (twice (!a)))
abbrev tailProgram (b : Bool) : Program sig true tailArm :=
  .split tailNext (.leaf (twice b)) (.leaf (twice (!b)))
abbrev pqHead : Program sig true headFirst := .split 0 (headProgram false) (headProgram true)
abbrev pqTail : Program sig true tailFirst := .split 2 (tailProgram false) (tailProgram true)

private theorem mixPure : Γmix.Pure := by unfold EffectCtx.Pure; decide
private theorem headTyped : Program.WellTyped sig strict pqHead :=
  ⟨⟨twice_typed false, twice_typed true⟩, ⟨twice_typed true, twice_typed false⟩⟩
private theorem tailTyped : Program.WellTyped sig strict pqTail :=
  ⟨⟨twice_typed false, twice_typed true⟩, ⟨twice_typed true, twice_typed false⟩⟩

private def requests : Expr Prim → Option (Nat × Nat)
  | .let₁ (.op .read (.pair (.var i) .unit)) (.op .read (.pair (.var j) .unit)) =>
      some (i, j - 1)
  | _ => none

-- Inspect the actual two requests after both splits, including removal of the
-- first response binder from the second request's index.
example : requests (twice false).source = some (0, 2) := rfl
example : requests (twice true).source = some (2, 0) := rfl

private theorem mixedEqv : Eqv Γmix outputSort strict pqHead.source pqTail.source := by
  have wp := Response.DecisionTree.source_wf sig mixPure strict pqHead headTyped
  have wq := Response.DecisionTree.source_wf sig mixPure strict pqTail tailTyped
  have hΓ : Γhead.Pure := SumSplit.branchCtx_pure mixPure 0 inputSort
  have wh (a : Bool) : Wf Γhead (headProgram a).source outputSort strict :=
    Response.DecisionTree.source_wf sig hΓ strict (headProgram a)
      ⟨twice_typed a, twice_typed (!a)⟩
  have eL := SumSplit.caseArms_left (Γ := Γmix) (i := 0) rfl rfl (wh false) (wh true)
  have eR := SumSplit.caseArms_right (Γ := Γmix) (i := 0) rfl rfl (wh false) (wh true)
  have hLeaf (rev : Bool) :
      Wf (SumSplit.branchCtx Γhead 2 inputSort) (twice rev).source outputSort strict :=
    source_wf sig (SumSplit.branchCtx_pure hΓ headNext inputSort) (leafSlots_typed false)
      strict (twice rev) (twice_typed rev)
  have hL0 := SumSplit.caseArms_left (i := tailNext) rfl rfl (hLeaf false) (hLeaf true)
  have hR0 := SumSplit.caseArms_right (i := tailNext) rfl rfl (hLeaf false) (hLeaf true)
  have hL1 := SumSplit.caseArms_left (i := tailNext) rfl rfl (hLeaf true) (hLeaf false)
  have hR1 := SumSplit.caseArms_right (i := tailNext) rfl rfl (hLeaf true) (hLeaf false)
  refine (SumSplit.eqv_iff_specializations (i := 0) rfl rfl wp wq).mpr ⟨?_, ?_⟩
  · refine eL.trans ?_
    exact (SumSplit.caseArms_eqv_iff headNext rfl rfl (hLeaf false) (hLeaf true)
      hL0.endpoints_wf.1 hL1.endpoints_wf.1).mpr ⟨hL0.symm, hL1.symm⟩
  · refine eR.trans ?_
    exact (SumSplit.caseArms_eqv_iff headNext rfl rfl (hLeaf true) (hLeaf false)
      hR0.endpoints_wf.1 hR1.endpoints_wf.1).mpr ⟨hR0.symm, hR1.symm⟩

/-- Opposite test orders agree at the strict bound. Both the native equality
and its mixed-shape reflection are checked on these concrete programs. -/
example : ∃ t s : Tm Empty Prim Γmix.length,
    pqHead.source.toLetIter Γmix.length = some t ∧ pqTail.source.toLetIter Γmix.length = some s ∧
    AbortEquiv (⊥ : Fx) Γ₀ Γmix.toBoundCtx t s outputSort ∧
    Eqv Γmix outputSort strict pqHead.source pqTail.source := by
  obtain ⟨t, ht, _⟩ := mixedEqv.endpoints_wf.1.toLetIter
  obtain ⟨s, hs, _⟩ := mixedEqv.endpoints_wf.2.toLetIter
  have hn := mixedEqv.toLetIter ht hs
  exact ⟨t, s, ht, hs, hn, (Response.DecisionTree.Reorder.endpoint_reflection sig mixPure
    strict pqHead pqTail headTyped tailTyped ht hs).mp hn⟩

end ReorderedDecisionTree

section EffectfulSumScrutinee

open Response (Atom extendSorts)
open Response.SumCall (SumSignature Program SumArgs SumResponse)

abbrev sumSig : SumSignature Bool Unit :=
  ⟨fun _ => 1, fun _ _ => false, fun _ => false, fun _ => true⟩

local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Prim ⊕ Unit) Fx := Response.SumCall.effects
local instance : HasTy (Prim ⊕ Unit) T := Response.SumCall.endpoints sig sumSig

abbrev outerArgs : SumArgs sig sumSig sorts () := fun _ => .var 1
abbrev leftResponseArm : Response.Sequence sig true (extendSorts false sorts) :=
  .call Prim.read (fun _ => .var 0) (.ret (.var 0))
abbrev rightResponseArm (next : Bool) : Response.Sequence sig true (extendSorts true sorts) :=
  .call Prim.readOther (fun _ => .var 0)
    (if next then .call Prim.readAlt (fun _ => .var 0) (.ret (.var 0))
      else .call Prim.read (fun _ => .var 0) (.ret (.var 0)))
abbrev sumProgram (next : Bool) : Program sig sumSig sorts true :=
  ⟨(), outerArgs, leftResponseArm, rightResponseArm next⟩

private theorem outerVisible (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

private theorem sumTyped (next : Bool) : Program.WellTyped sig sumSig strict (sumProgram next) := by
  have hr : ¬ IsPure (⊥ : Fx) Prim.readAlt := by
    change strict ≠ (⊥ : Fx)
    decide
  cases next
  · exact ⟨fun _ => trivial, le_rfl,
      ⟨fun _ => trivial, read_not_pure, le_rfl, trivial⟩,
      ⟨fun _ => trivial, read_other_not_pure, le_rfl,
        fun _ => trivial, read_not_pure, le_rfl, trivial⟩⟩
  · exact ⟨fun _ => trivial, le_rfl,
      ⟨fun _ => trivial, read_not_pure, le_rfl, trivial⟩,
      ⟨fun _ => trivial, read_other_not_pure, le_rfl,
        fun _ => trivial, hr, le_rfl, trivial⟩⟩

/-- Observe exactly one outer request, then distinct first requests in the two
arms. The right arm uses its first call's response in its next request. -/
example :
    ∃ d : Derivation (Prim ⊕ Unit) Γ₀ Γ.toBoundCtx (sumProgram true).native outputSort,
    ∃ k : SumResponse sig sumSig sorts () →
        ITree.Tree (Response.SumCall.Event sig sumSig sorts) (Atom sig sorts true),
      d.denote (Ty.denote (Atom sig sorts)) (Response.SumCall.instructions (ε := Fx) sig sumSig sorts)
          (fun x => x.elim) (Response.variableEnv sig sorts slots_typed Tree.var) =
          ITree.vis (.sum () outerArgs) k ∧
      (∀ a, k (.inl a) = ITree.vis (.atom Prim.read (fun _ => a)) (fun b => ITree.ret ⟨b⟩)) ∧
      (∀ a, k (.inr a) = ITree.vis (.atom Prim.readOther (fun _ => a)) (fun b =>
        ITree.vis (.atom Prim.readAlt (fun _ => b)) (fun c => ITree.ret ⟨c⟩))) := by
  obtain ⟨d, hd⟩ := Response.SumCall.eval_exists sig sumSig sorts slots_typed strict
    (sumProgram true) (sumTyped true)
  exact ⟨d, _, (hd Tree.var).trans rfl, fun _ => rfl, fun _ => rfl⟩

private def secondRequest {n : Nat} {ss : Fin n → Bool} : Response.Sequence sig true ss → Option Prim
  | .call _ _ (.call f _ _) => some f
  | _ => none

/-- Equal outer requests and equal left arms still expose the changed second
request of the right arm. This runs through native soundness and both tagged
response observations at the strict bound. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    (sumProgram true).native (sumProgram false).native outputSort := by
  intro h
  have he := Response.SumCall.native_eq_implies_eq sig sumSig outerVisible slots_typed strict
    (sumProgram true) (sumProgram false) (sumTyped true) (sumTyped false) h
  have hs : some Prim.readAlt = some Prim.read :=
    congrArg (fun (p : Program sig sumSig sorts true) => secondRequest p.right) he
  cases hs

example : AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    (sumProgram true).native (sumProgram false).native outputSort ↔
    Eqv Γ outputSort strict (sumProgram true).source (sumProgram false).source :=
  Response.SumCall.endpoint_reflection sig sumSig outerVisible ctx_pure slots_typed strict
    (sumProgram true) (sumProgram false) (sumTyped true) (sumTyped false)

section ResponseDependentRequest

abbrev afterRead := extendSorts false sorts

abbrev subsequentArgs (fromReply : Bool) : SumArgs sig sumSig afterRead () :=
  if fromReply then fun _ => .var 0 else fun _ => .var 2

abbrev mixedProgram (fromReply : Bool) : Response.Mixed.Program sig sumSig true sorts :=
  .atom Prim.readOther (fun _ => .var 0)
    (.sum () (subsequentArgs fromReply)
      (.atom Prim.read (fun _ => .var 0) (.ret (.var 0)))
      (.atom Prim.readOther (fun _ => .var 0)
        (.atom Prim.readAlt (fun _ => .var 0) (.ret (.var 0)))))

private theorem mixedTyped (fromReply : Bool) :
    Response.Mixed.Program.WellTyped sig sumSig strict (mixedProgram fromReply) := by
  have hAlt : ¬ IsPure (⊥ : Fx) Prim.readAlt := by
    change strict ≠ (⊥ : Fx)
    decide
  have hArgs : ∀ i, DeclaredPure (ε := Fx) sig (subsequentArgs fromReply i) := by
    cases fromReply <;> exact fun _ => trivial
  exact ⟨fun _ => trivial, read_other_not_pure, le_rfl, hArgs, le_rfl,
    ⟨fun _ => trivial, read_not_pure, le_rfl, trivial⟩,
    ⟨fun _ => trivial, read_other_not_pure, le_rfl, fun _ => trivial, hAlt, le_rfl, trivial⟩⟩

/-- The second visible request uses the actual first reply as its argument.
The response tag of that request then chooses the next request. -/
example :
    ∃ d : Derivation (Prim ⊕ Unit) Γ₀ Γ.toBoundCtx (mixedProgram true).native outputSort,
    ∃ k : Tree sig sorts false →
        ITree.Tree (Response.SumCall.Event sig sumSig sorts) (Atom sig sorts true),
      d.denote (Ty.denote (Atom sig sorts)) (Response.SumCall.instructions (ε := Fx) sig sumSig sorts)
          (fun x => x.elim) (Response.variableEnv sig sorts slots_typed Tree.var) =
          ITree.vis (.atom Prim.readOther (fun _ => Tree.var 0)) k ∧
      ∀ reply, ∃ branch : SumResponse sig sumSig sorts () →
          ITree.Tree (Response.SumCall.Event sig sumSig sorts) (Atom sig sorts true),
        k reply = ITree.vis (.sum () (fun _ => reply)) branch ∧
        (∀ a, branch (.inl a) = ITree.vis (.atom Prim.read (fun _ => a)) (fun b => ITree.ret ⟨b⟩)) ∧
        (∀ a, branch (.inr a) = ITree.vis (.atom Prim.readOther (fun _ => a)) (fun b =>
          ITree.vis (.atom Prim.readAlt (fun _ => b)) (fun c => ITree.ret ⟨c⟩))) := by
  obtain ⟨d, hd⟩ := Response.Mixed.eval_exists sig sumSig sorts slots_typed strict
    (mixedProgram true) (mixedTyped true)
  exact ⟨d, _, (hd Tree.var).trans rfl, fun _ => ⟨_, rfl, fun _ => rfl, fun _ => rfl⟩⟩

private def treeSlot {n : Nat} {ss : Fin n → Bool} {a : Bool} : Tree sig ss a → Option Nat
  | .var i => some i.val
  | .op _ _ => none

private def sumArgSlot : Response.Mixed.Program sig sumSig true sorts → Option Nat
  | .atom _ _ (.sum _ args _ _) => treeSlot (args 0)
  | _ => none

private theorem reply_distinguished :
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (mixedProgram true).native
      (mixedProgram false).native outputSort := by
  intro h
  have he := Response.Mixed.native_eq_implies_eq sig sumSig outerVisible slots_typed strict
    (mixedProgram true) (mixedProgram false) (mixedTyped true) (mixedTyped false) h
  have hslots : (some 0 : Option Nat) = some 2 := congrArg sumArgSlot he
  cases hslots

/-- Replacing the response by an ambient variable of the same sort changes
the source class at the same strict bound. -/
example : ¬ Eqv Γ outputSort strict (mixedProgram true).source (mixedProgram false).source := by
  intro he
  exact reply_distinguished ((Response.Mixed.endpoint_reflection sig sumSig outerVisible ctx_pure
    slots_typed strict (mixedProgram true) (mixedProgram false) (mixedTyped true) (mixedTyped false)).mpr he)

end ResponseDependentRequest

section RawSumResponseArms


abbrev payloadRead : Response.Flatten.Program sig (extendSorts true sorts) false :=
  .request Prim.readOther (fun _ => .var 0)
abbrev argumentRead : Response.Flatten.Program sig (extendSorts false (extendSorts true sorts)) true :=
  .request Prim.readAlt (fun _ => .var 0)
abbrev nestedRaw : Response.Mixed.RawArms.Program sig sumSig sorts true :=
  ⟨(), outerArgs, .request Prim.read (fun _ => .var 0), .unary Prim.readAlt rfl payloadRead⟩
abbrev sequencedRaw : Response.Mixed.RawArms.Program sig sumSig sorts true :=
  ⟨(), outerArgs, .request Prim.read (fun _ => .var 0), .let1 payloadRead argumentRead⟩

private theorem nestedRaw_typed : Response.Mixed.RawArms.Program.WellTyped sig sumSig strict nestedRaw :=
  ⟨fun _ => trivial, le_rfl, ⟨le_rfl, fun _ => trivial⟩, le_rfl, le_rfl, fun _ => trivial⟩
private theorem sequencedRaw_typed : Response.Mixed.RawArms.Program.WellTyped sig sumSig strict sequencedRaw :=
  ⟨fun _ => trivial, le_rfl, ⟨le_rfl, fun _ => trivial⟩,
    ⟨le_rfl, fun _ => trivial⟩, le_rfl, fun _ => trivial⟩

private theorem sameArmCompile : Response.Flatten.compile (ε := Fx) sig nestedRaw.right =
    Response.Flatten.compile (ε := Fx) sig sequencedRaw.right := by
  have hArgs :
      Response.Flatten.unaryArgs sig (f := Prim.readAlt) rfl
        (Tree.var (S := sig) (sorts := extendSorts false (extendSorts true sorts)) 0) =
      (fun _ => Tree.var (S := sig) (sorts := extendSorts false (extendSorts true sorts)) 0) := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  simp only [nestedRaw, sequencedRaw, Response.Flatten.compile, Response.Flatten.unaryTail, hArgs]

private theorem sameCompile : Response.Mixed.RawArms.Program.compile (ε := Fx) sig sumSig nestedRaw =
    Response.Mixed.RawArms.Program.compile (ε := Fx) sig sumSig sequencedRaw := by
  exact congrArg (fun arm => Response.Mixed.Program.sum (S := sig) (T := sumSig) () outerArgs
    (Response.Mixed.ofSequence sig sumSig (Response.Flatten.compile (ε := Fx) sig nestedRaw.left))
    (Response.Mixed.ofSequence sig sumSig arm)) sameArmCompile

/-- The raw lowering passes the selected right payload to readOther, nested
inside the argument of readAlt. -/
example : nestedRaw.source.toLetIter Γ.length = some
    (.case (.op (.inr ()) (.pair (.bv 1) .unit))
      (.op (.inl Prim.read) (.pair (.bv 0) .unit))
      (.op (.inl Prim.readAlt) (.pair (.op (.inl Prim.readOther) (.pair (.bv 0) .unit)) .unit))) :=
  rfl

/-- The inner read uses the payload at slot zero. Its response becomes
the argument of the second request. -/
example : Response.Flatten.compile (ε := Fx) sig nestedRaw.right = rightResponseArm true := by
  rw [sameArmCompile]
  simp only [sequencedRaw, Response.Flatten.compile, Response.Flatten.emit,
    ite_eq_right read_other_not_pure, ite_eq_right read_alt_not_pure,
    Response.Sequence.bind, Response.Sequence.subst]
  rfl

/-- The explicit let and the nested argument are equal at the strict bound.
Both native endpoints keep that bound, and the raw endpoint theorem reflects
their equality. -/
example : ∃ t s : Tm Empty (Prim ⊕ Unit) Γ.length,
    nestedRaw.source.toLetIter Γ.length = some t ∧ sequencedRaw.source.toLetIter Γ.length = some s ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx t outputSort strict ∧ HasTypeEffect Γ₀ Γ.toBoundCtx s outputSort strict ∧
    AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort ∧
    Eqv Γ outputSort strict nestedRaw.source sequencedRaw.source := by
  let h := Response.Mixed.RawArms.source_wf sig sumSig (c := true) ctx_pure slots_typed strict
  obtain ⟨t, ht, _⟩ := (h nestedRaw nestedRaw_typed).toLetIter
  obtain ⟨s, hs, _⟩ := (h sequencedRaw sequencedRaw_typed).toLetIter
  obtain ⟨hpt, _, hp⟩ := Response.Mixed.RawArms.compile_native sig sumSig ctx_pure slots_typed strict
    nestedRaw nestedRaw_typed ht
  obtain ⟨hqt, _, hq⟩ := Response.Mixed.RawArms.compile_native sig sumSig ctx_pure slots_typed strict
    sequencedRaw sequencedRaw_typed hs
  have hq' := sameCompile.symm ▸ hq
  have hn := hp.trans hq'.symm
  exact ⟨t, s, ht, hs, hpt, hqt, hn,
    (Response.Mixed.RawArms.endpoint_reflection sig sumSig outerVisible ctx_pure slots_typed strict
      nestedRaw sequencedRaw nestedRaw_typed sequencedRaw_typed ht hs).mp hn⟩

end RawSumResponseArms

section RawMixedPrefix

abbrev argumentInLeft : Response.Flatten.Program sig (extendSorts false sorts) false :=
  .unary Prim.readOther rfl (.request Prim.read (fun _ => .var 0))

abbrev secondLeft : Response.Mixed.Raw.Program sig sumSig true (extendSorts false (extendSorts false sorts)) :=
  .straight (.request Prim.readAlt (fun _ => .var 1))
abbrev secondRight : Response.Mixed.Raw.Program sig sumSig true (extendSorts true (extendSorts false sorts)) :=
  .straight (.tree (.var 0))
abbrev shiftedLeft : Response.Mixed.Raw.Program sig sumSig true
    (extendSorts false (extendSorts false (extendSorts false sorts))) :=
  .straight (.request Prim.readAlt (fun _ => .var 2))
abbrev shiftedRight : Response.Mixed.Raw.Program sig sumSig true
    (extendSorts true (extendSorts false (extendSorts false sorts))) :=
  .straight (.tree (.var 0))

abbrev nestedInLeft : Response.Mixed.Raw.Program sig sumSig true (extendSorts false sorts) :=
  .sumUnary () rfl argumentInLeft secondLeft secondRight
abbrev explicitInLeft : Response.Mixed.Raw.Program sig sumSig true (extendSorts false sorts) :=
  .let1 argumentInLeft (.sum () (fun _ => .var 0) shiftedLeft shiftedRight)

abbrev rawNestedTree : Response.Mixed.Raw.Program sig sumSig true sorts :=
  .sum () outerArgs nestedInLeft (.straight (.tree (.var 0)))
abbrev rawPrefixTree : Response.Mixed.Raw.Program sig sumSig true sorts :=
  .sum () outerArgs explicitInLeft (.straight (.tree (.var 0)))

private theorem rawNestedTree_typed : Response.Mixed.Raw.Program.WellTyped sig sumSig strict rawNestedTree := by
  refine ⟨fun _ => trivial, le_rfl, ?_, trivial⟩
  exact ⟨⟨le_rfl, le_rfl, fun _ => trivial⟩, le_rfl, ⟨le_rfl, fun _ => trivial⟩, trivial⟩

private theorem rawPrefixTree_typed : Response.Mixed.Raw.Program.WellTyped sig sumSig strict rawPrefixTree := by
  refine ⟨fun _ => trivial, le_rfl, ?_, trivial⟩
  exact ⟨⟨le_rfl, le_rfl, fun _ => trivial⟩, fun _ => trivial, le_rfl, ⟨le_rfl, fun _ => trivial⟩, trivial⟩

private theorem rawMixedSameCompile :
    Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig rawNestedTree =
      Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig rawPrefixTree := by
  have ha : Response.Mixed.Raw.unaryVarArgs sig sumSig (g := ()) (slots := extendSorts false sorts) rfl =
      (fun _ => .var 0) := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  have hl : Response.Mixed.weakenUnder sig sumSig false
      (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondLeft) =
      Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedLeft := by
    simp only [Response.Mixed.Raw.Program.compile, Response.Flatten.compile,
      Response.Flatten.emit, ite_eq_right read_alt_not_pure, Response.Mixed.ofSequence,
      Response.Mixed.weakenUnder, Response.Mixed.subst]
    rfl
  have hr : Response.Mixed.weakenUnder sig sumSig false
      (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondRight) =
      Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedRight := rfl
  have hbody :
      (Response.Mixed.Program.sum (S := sig) (T := sumSig) ()
        (Response.Mixed.Raw.unaryVarArgs sig sumSig (slots := extendSorts false sorts) rfl)
        (Response.Mixed.weakenUnder sig sumSig false
          (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondLeft))
        (Response.Mixed.weakenUnder sig sumSig false
          (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondRight))) =
      .sum () (fun _ => .var 0) (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedLeft)
        (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedRight) := by
    rw [ha, hl, hr]
  exact congrArg (fun body => Response.Mixed.Program.sum (S := sig) (T := sumSig) () outerArgs
    (Response.Mixed.bindPrefix sig sumSig (Response.Flatten.compile (ε := Fx) sig argumentInLeft) body)
    (.ret (.var 0))) hbody

/-- A second sum request is inside the first left arm. Its argument contains
two nested atomic calls and uses that first payload at slot zero. -/
example : rawNestedTree.source.toLetIter Γ.length = some
    (.case (.op (.inr ()) (.pair (.bv 1) .unit))
      (.case (.op (.inr ())
        (.pair (.op (.inl Prim.readOther) (.pair (.op (.inl Prim.read) (.pair (.bv 0) .unit)) .unit)) .unit))
        (.op (.inl Prim.readAlt) (.pair (.bv 1) .unit)) (.bv 0))
      (.bv 0)) := rfl

private def compiledLeftRequests (p : Response.Mixed.Program sig sumSig true sorts) : List (Option Nat) :=
  match p with
  | .sum _ _ (.atom .read first (.atom .readOther next (.sum _ arg (.atom .readAlt retained _) _))) _ =>
    [treeSlot (first 0), treeSlot (next 0), treeSlot (arg 0), treeSlot (retained 0)]
  | _ => []

/-- The normalized branch passes each new reply into the next request.
After the second split, slot three still points to the first sum payload. -/
example : compiledLeftRequests (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig rawNestedTree) =
    [some 0, some 0, some 0, some 3] := by
  simp only [Response.Mixed.Raw.Program.compile, Response.Flatten.compile, Response.Flatten.unaryTail,
    Response.Flatten.emit, ite_eq_right read_not_pure, ite_eq_right read_other_not_pure,
    ite_eq_right read_alt_not_pure, Response.Sequence.bind, Response.Sequence.subst,
    Response.Mixed.bindPrefix, Response.Mixed.ofSequence, Response.Mixed.weakenUnder, Response.Mixed.subst]
  rfl

/-- Both raw trees stay at the strict bound, including the nested argument
and the arm that retains the earlier payload. -/
example : ∃ t s : Tm Empty (Prim ⊕ Unit) Γ.length,
    rawNestedTree.source.toLetIter Γ.length = some t ∧ rawPrefixTree.source.toLetIter Γ.length = some s ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx t outputSort strict ∧ HasTypeEffect Γ₀ Γ.toBoundCtx s outputSort strict ∧
    AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort ∧
    Eqv Γ outputSort strict rawNestedTree.source rawPrefixTree.source := by
  let h := Response.Mixed.Raw.source_wf sig sumSig (c := true) ctx_pure slots_typed strict
  obtain ⟨t, ht, _⟩ := (h rawNestedTree rawNestedTree_typed).toLetIter
  obtain ⟨s, hs, _⟩ := (h rawPrefixTree rawPrefixTree_typed).toLetIter
  obtain ⟨ht', _, hp⟩ := Response.Mixed.Raw.compile_native sig sumSig ctx_pure slots_typed strict
    rawNestedTree rawNestedTree_typed ht
  obtain ⟨hs', _, hq⟩ := Response.Mixed.Raw.compile_native sig sumSig ctx_pure slots_typed strict
    rawPrefixTree rawPrefixTree_typed hs
  have hq' := rawMixedSameCompile.symm ▸ hq
  have hn := hp.trans hq'.symm
  exact ⟨t, s, ht, hs, ht', hs', hn,
    (Response.Mixed.Raw.endpoint_reflection sig sumSig outerVisible ctx_pure slots_typed strict
      rawNestedTree rawPrefixTree rawNestedTree_typed rawPrefixTree_typed ht hs).mp hn⟩

end RawMixedPrefix

end EffectfulSumScrutinee

end LetIterResponseSingleCall

namespace LetIterRankedFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev A : Ty Unit := .base ()
abbrev X : Ty Unit := .coprod .unit .unit
abbrev R : Ty Unit := .coprod A X
abbrev sig : Signature Unit Empty := ⟨Empty.elim, fun e => e.elim, Empty.elim⟩
abbrev sumSig : SumCall.SumSignature Unit Unit := ⟨fun _ => 0, fun _ i => i.elim0, fun _ => (), fun _ => ()⟩
abbrev free := (Ctx.nil : Ctx Empty (Ty Unit))
abbrev Term n := Tm Empty (Empty ⊕ Unit) n

local instance : HasEff Empty Fx := ⟨Empty.elim⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Empty ⊕ Unit) Fx := SumCall.effects
local instance : HasTy (Empty ⊕ Unit) (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev state (i : Bool) (n : Nat) : Term n :=
  if i then .inr .unit else .inl .unit
abbrev ask (n : Nat) : Term n := .op (.inr ()) .unit

-- The `true` state repeats on the right reply, while the `false` state
-- makes its own request and exits on either reply.
abbrev replyStep (i : Bool) (n : Nat) : Term n :=
  .case (ask n) (.inl (.bv 0)) (if i then .inr (state false (n + 1)) else .inl (.bv 0))
abbrev loopBody (n : Nat) : Term (n + 1) :=
  .case (.bv 0) (replyStep false (n + 2)) (replyStep true (n + 2))
abbrev loop (i : Bool) (n : Nat) : Term n := .iter (state i n) (loopBody n)
abbrev restart (n : Nat) : Term (n + 1) := .iter (.bv 0) (loopBody (n + 1))
abbrev dispatch (n : Nat) : Term (n + 1) := .case (.bv 0) (.bv 0) (restart (n + 1))

private theorem stateTy {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    HasType (Empty ⊕ Unit) free β (state i n) X := by
  cases i
  · exact .inl .unit
  · exact .inr .unit

private theorem replyTy {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    HasType (Empty ⊕ Unit) free β (replyStep i n) R := by
  cases i
  · exact .case (.op .unit) (.inl .bv) (.inl .bv)
  · exact .case (.op .unit) (.inl .bv) (.inr (.inl .unit))

private theorem bodyTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β X) (loopBody n) R :=
  .case (A := (Ty.unit : Ty Unit)) (B := Ty.unit) .bv (replyTy _ false) (replyTy _ true)

private theorem restartTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β X) (restart n) A :=
  .iter .bv (bodyTy _)

private theorem dispatchTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β R) (dispatch n) A :=
  .case (A := A) (B := X) .bv .bv (restartTy _)

private theorem selectState {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    Equiv (⊥ : Fx) free β
      (.case (state i n) (replyStep false (n + 1)) (replyStep true (n + 1))) (replyStep i n) R := by
  cases i
  · exact (Equiv.caseBetaL (B := (Ty.unit : Ty Unit)) .unit (replyTy _ false) (replyTy _ true)).trans
      (Equiv.letBeta .unit .unit (replyTy _ false))
  · exact (Equiv.caseBetaR (A := (Ty.unit : Ty Unit)) .unit (replyTy _ false) (replyTy _ true)).trans
      (Equiv.letBeta .unit .unit (replyTy _ true))

private theorem unfoldLoop {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    Equiv (⊥ : Fx) free β (loop i n) (.case (replyStep i n) (.bv 0) (restart n)) A := by
  have hfix := Equiv.fixpoint (pureEff := (⊥ : Fx)) (stateTy β i) (bodyTy β)
  have hp : Pure (⊥ : Fx) (state i n) := by
    cases i
    · exact .inl .unit
    · exact .inr .unit
  have hw : HasType (Empty ⊕ Unit) free (.snoc β X)
      (.case (loopBody n) (.bv 0) (restart (n + 1))) A :=
    .case (A := A) (B := X) (bodyTy β) .bv (restartTy _)
  have h₁ := hfix.trans (Equiv.letBeta hp (stateTy β i) hw)
  exact h₁.trans (.case (selectState β i) (.refl .bv) (.refl (restartTy β)))

abbrev replyLeft (n : Nat) : Term (n + 1) := .inl (.bv 0)
abbrev replyRight (i : Bool) (n : Nat) : Term (n + 1) :=
  if i then .inr (state false (n + 1)) else replyLeft n

private theorem leftTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β A) (replyLeft n) R :=
  .inl .bv

private theorem rightTy {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    HasType (Empty ⊕ Unit) free (.snoc β A) (replyRight i n) R := by
  cases i
  · exact leftTy β
  · exact .inr (stateTy _ false)

private theorem returnReply {n : Nat} (β : BoundCtx (Ty Unit) n) :
    Equiv (⊥ : Fx) free (.snoc β A) (.let₁ (replyLeft n) (dispatch (n + 1))) (.bv 0) A := by
  have h := Equiv.letBeta (pureEff := (⊥ : Fx)) (.inl .bv) (leftTy β) (dispatchTy (.snoc β A))
  exact h.trans ((Equiv.caseBetaL (.bv (ι := 0)) .bv (restartTy _)).trans (Equiv.letEta .bv))

private theorem repeatReply {n : Nat} (β : BoundCtx (Ty Unit) n) :
    Equiv (⊥ : Fx) free (.snoc β A) (.let₁ (replyRight true n) (dispatch (n + 1))) (loop false (n + 1)) A := by
  have h := Equiv.letBeta (pureEff := (⊥ : Fx)) (.inr (.inl .unit)) (rightTy β true) (dispatchTy (.snoc β A))
  have hcase := Equiv.caseBetaR (pureEff := (⊥ : Fx)) (A := A)
    (stateTy (.snoc β A) false) (.bv (ι := 0)) (restartTy (.snoc β A))
  have hbeta := Equiv.letBeta (pureEff := (⊥ : Fx)) (.inl .unit)
    (stateTy (.snoc β A) false) (restartTy (.snoc β A))
  exact h.trans (hcase.trans hbeta)

private theorem simplifyReply {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    Equiv (⊥ : Fx) free β (.case (replyStep i n) (.bv 0) (restart n))
      (.case (ask n) (.bv 0) (if i then loop false (n + 1) else .bv 0)) A := by
  have h :=
    Equiv.bindCase (pureEff := (⊥ : Fx)) (replyTy β i) (.bv (ι := 0)) (restartTy β)
  have hAsk : HasType (Empty ⊕ Unit) free β (ask n) (.coprod A A) := .op .unit
  have h' := Equiv.bindLetCase (pureEff := (⊥ : Fx)) hAsk (leftTy β) (rightTy β i) (dispatchTy β)
  refine h.trans (h'.trans (.case (.refl hAsk) (returnReply β) ?_))
  cases i
  · exact returnReply β
  · exact repeatReply β

def rank : Bool → Nat
  | false => 0
  | true => 1

abbrev finish {n : Nat} {ss : Fin n → Unit} :
    Mixed.Raw.Program sig sumSig () (extendSorts () ss) := .straight (.tree (.var 0))

def sys : Mixed.Ranked.System sig sumSig rank () where
  endpoint := fun {n} _ i => loop i n
  step := fun _ i => match i with
    | false => .sum () (fun i => i.elim0) (.done finish) (.done finish)
    | true => .sum () (fun i => i.elim0) (.done finish) (.again false (by decide))

private theorem sumVisible (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

private theorem sys_checked : Mixed.Ranked.System.Checked sig sumSig rank sys strict := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ss i
    cases i
    · exact ⟨fun j => j.elim0, le_rfl, trivial, trivial⟩
    · exact ⟨fun j => j.elim0, le_rfl, trivial, trivial⟩
  · intro Γ ss hΓ hs i
    refine ⟨.iter (stateTy Γ.toBoundCtx i) (bodyTy Γ.toBoundCtx), ?_⟩
    cases i <;> exact le_rfl
  · intro Γ ss hΓ hs i
    have h := (unfoldLoop Γ.toBoundCtx i).trans (simplifyReply Γ.toBoundCtx i)
    cases i
    · exact .equiv h
    · exact .equiv h

abbrev returnEither {n : Nat} {ss : Fin n → Unit} : Mixed.Raw.Program sig sumSig () ss :=
  .sum () (fun j => j.elim0) finish finish

/-- Only the right reply causes a second request, in the smaller state. -/
abbrev unrolled {n : Nat} {ss : Fin n → Unit} : Mixed.Raw.Program sig sumSig () ss :=
  .sum () (fun j => j.elim0) finish returnEither

private theorem unrolledTyped {n : Nat} (ss : Fin n → Unit) :
    Mixed.Raw.Program.WellTyped sig sumSig strict (unrolled (ss := ss)) :=
  ⟨fun j => j.elim0, le_rfl, trivial, fun j => j.elim0, le_rfl, trivial, trivial⟩

private theorem expandFalse {n : Nat} (ss : Fin n → Unit) :
    Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys false ss =
      Mixed.Raw.Program.compile (ε := Fx) sig sumSig (returnEither (ss := ss)) := by
  rw [Mixed.Ranked.System.expand_step]
  rfl

private theorem expandTrue {n : Nat} (ss : Fin n → Unit) :
    Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys true ss =
      Mixed.Raw.Program.compile (ε := Fx) sig sumSig (unrolled (ss := ss)) := by
  rw [Mixed.Ranked.System.expand_step]
  change Mixed.Program.sum (S := sig) (T := sumSig) () (fun j => j.elim0) (.ret (.var 0))
    (Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys false (extendSorts () ss)) = _
  rw [expandFalse]
  rfl

abbrev Γ : EffectCtx (Ty Unit) Fx := []
abbrev slots : Fin Γ.length → Unit := Fin.elim0

/-- The local equation retains a native iteration only at the right reply. -/
example : Mixed.Ranked.Step.native (ε := Fx) sig sumSig rank sys.endpoint (sys.step slots true) =
    .case (ask Γ.length) (.bv 0) (loop false (Γ.length + 1)) :=
  rfl

/-- Native fixpoint expansion and source reflection at the strict effect
bound. The right tag of the first visible request takes the repeat site. -/
example : ∃ t : Term Γ.length, (unrolled (ss := slots)).source.toLetIter Γ.length = some t ∧
    HasTypeEffect free Γ.toBoundCtx (loop true Γ.length) A strict ∧
    HasTypeEffect free Γ.toBoundCtx t A strict ∧
    AbortEquiv (⊥ : Fx) free Γ.toBoundCtx (loop true Γ.length) t A ∧
    Eqv Γ A strict (Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys true slots).source
      (unrolled (ss := slots)).source := by
  have hΓ : Γ.Pure := fun i => i.elim0
  have hs : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0
  let p := unrolled (ss := slots)
  have hp := unrolledTyped slots
  obtain ⟨t, ht, ht'⟩ := (Mixed.Raw.source_wf sig sumSig hΓ hs strict p hp).toLetIter
  have h := Mixed.Ranked.raw_endpoint_reflection sig sumSig rank sumVisible sys strict sys_checked
    true hΓ hs p hp ht
  have he : Eqv Γ A strict (Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys true slots).source p.source := by
    rw [expandTrue]
    exact (Mixed.Raw.compile_eqv sig sumSig hΓ hs strict p hp).symm
  have htLoop := (Mixed.Ranked.expand_native sig sumSig rank sys strict sys_checked true hΓ hs).1
  exact ⟨t, ht, htLoop, ht', h.mpr he, h.mp (h.mpr he)⟩

end LetIterRankedFixture

namespace LetIterCompiledRankedFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open Mixed.Ranked.Compile

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev sig : Signature Unit Unit := ⟨fun _ => 1, fun _ _ => (), fun _ => ()⟩
abbrev sumSig : SumCall.SumSignature Unit Unit :=
  ⟨fun _ => 0, fun _ i => i.elim0, fun _ => (), fun _ => ()⟩
abbrev A : Ty Unit := .base ()
abbrev free := (Ctx.nil : Ctx Empty (Ty Unit))
abbrev Γ : EffectCtx (Ty Unit) Fx := [(A, ⊥)]
abbrev slots : Fin Γ.length → Unit := fun _ => ()

local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Unit ⊕ Unit) Fx := SumCall.effects
local instance : HasTy (Unit ⊕ Unit) (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

private theorem visible (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

/-- State 1 branches on a visible sum reply. The right arm re-enters state 0
with that reply. The unary request of state 0 uses the carried payload. -/
def controller : Controller sig sumSig () () 1 :=
  Fin.cases (motive := fun j => Body sig sumSig () () 1 j.val (fun _ : Fin 1 => ()))
    (.atom () (fun _ => .var 0) (.done (.var 0)))
    (fun j => .sum () (fun i => i.elim0) (.done (.var 0))
      (.again 0 (Nat.zero_lt_succ j.val) (.var 0)))

private theorem controllerTyped (j : Fin 2) : Body.WellTyped sig sumSig strict (controller j) := by
  refine Fin.cases (motive := fun j => Body.WellTyped sig sumSig strict (controller j)) ?_ ?_ j
  · exact ⟨fun _ => trivial, visible (), le_rfl, trivial⟩
  · exact fun _ => ⟨fun i => i.elim0, le_rfl, trivial, trivial⟩

def start : Entry sig Fx () 1 slots := ⟨(0 : Fin 1).succ, .var 0, by trivial⟩

def afterReply : Entry sig Fx () 1 (extendSorts () slots) := ⟨0, .var 0, by trivial⟩

abbrev system := controller.system sig sumSig strict controllerTyped

private theorem stepStart :
    system.step slots start =
      .sum () (fun j => j.elim0) (.done (.straight (.tree (.var 0)))) (.again afterReply (by decide)) := by
  simp only [system, Controller.system, start, controller, Fin.cases_succ, Body.toStep, Tree.interpret]
  congr 1
  funext i
  exact i.elim0

private theorem stepAfterReply :
    system.step (extendSorts () slots) afterReply =
      .atom () (fun _ => .var 0) (.done (.straight (.tree (.var 0)))) := rfl

abbrev explicit : Mixed.Raw.Program sig sumSig () slots :=
  .sum () (fun j => j.elim0) (.straight (.tree (.var 0)))
    (.straight (.request () (fun _ => .var 0)))

private theorem explicitTyped : explicit.WellTyped sig sumSig strict :=
  ⟨fun j => j.elim0, le_rfl, trivial, le_rfl, fun _ => trivial⟩

/-- The smaller state uses index zero, the selected payload, even though
index one still refers to the original loop entry's payload. -/
example :
    Mixed.Ranked.Scoped.Step.native (ε := Fx) sig sumSig (@entryRank _ _ sig () 1 Fx _ _)
      (controller.system sig sumSig strict controllerTyped).endpoint
      ((controller.system sig sumSig strict controllerTyped).step slots start) =
    (.case (.op (.inr ()) .unit) (.bv 0)
      (.iter (.inl (.bv 0)) (controller.loopBody sig sumSig (Γ.length + 1)))) :=
  rfl

private theorem expansion_eq :
    controller.expansion sig sumSig strict controllerTyped start = explicit.compile sig sumSig (ε := Fx) := by
  unfold Controller.expansion
  rw [Mixed.Ranked.Scoped.System.expand_step, stepStart]
  simp only [Mixed.Ranked.Scoped.Step.expand, Mixed.Raw.Program.compile, Flatten.compile, Mixed.ofSequence]
  rw [Mixed.Ranked.Scoped.System.expand_step, stepAfterReply]
  simp [Mixed.Ranked.Scoped.Step.expand, Mixed.Raw.Program.compile, Flatten.compile, Flatten.emit,
    Mixed.ofSequence, visible]

example : ∃ t : Tm Empty (Unit ⊕ Unit) Γ.length, explicit.source.toLetIter Γ.length = some t ∧
    HasTypeEffect free Γ.toBoundCtx (controller.loop sig sumSig start) A strict ∧
    AbortEquiv (⊥ : Fx) free Γ.toBoundCtx (controller.loop sig sumSig start) t A ∧
    Eqv Γ A strict (controller.expansion sig sumSig strict controllerTyped start).source explicit.source := by
  have hΓ : Γ.Pure := fun i => Fin.cases rfl (fun j => j.elim0) i
  have hs : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots i) :=
    fun i => Fin.cases rfl (fun j => j.elim0) i
  have he : IsIterative strict := rfl
  obtain ⟨t, ht, _⟩ := (Mixed.Raw.source_wf sig sumSig hΓ hs strict explicit explicitTyped).toLetIter
  have h := raw_endpoint_reflection sig sumSig visible strict he controller controllerTyped
    hΓ hs start explicit explicitTyped ht
  have heq : Eqv Γ A strict (controller.expansion sig sumSig strict controllerTyped start).source explicit.source := by
    rw [expansion_eq]
    exact (Mixed.Raw.compile_eqv sig sumSig hΓ hs strict explicit explicitTyped).symm
  exact ⟨t, ht, (controller.checked sig sumSig strict he controllerTyped).endpoint_typed hΓ hs start,
    h.mpr heq, h.mp (h.mpr heq)⟩

end LetIterCompiledRankedFixture

namespace LetIterCyclicFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open LetIterRankedFixture

local instance : HasEff Empty Fx := ⟨Empty.elim⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Empty ⊕ Unit) Fx := SumCall.effects
local instance : HasTy (Empty ⊕ Unit) (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev cycle : Term Γ.length := Mixed.repeatOnRight () Γ.length

private theorem cycleTyped : HasTypeEffect free Γ.toBoundCtx cycle A strict :=
  Mixed.repeatOnRight_typed sig sumSig rfl strict le_rfl rfl

/-- The candidate makes the same first request and returns on either reply.
The loop can repeat on the right at the same strict effect bound. -/
example :
    ∃ t : Term Γ.length, (returnEither (ss := slots)).source.toLetIter Γ.length = some t ∧
      HasTypeEffect free Γ.toBoundCtx cycle A strict ∧ HasTypeEffect free Γ.toBoundCtx t A strict ∧
      ¬ AbortEquiv (⊥ : Fx) free Γ.toBoundCtx cycle t A := by
  have hΓ : Γ.Pure := fun i => i.elim0
  have hs : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0
  let p := returnEither (ss := slots)
  have hp : p.WellTyped sig sumSig strict := ⟨fun i => i.elim0, le_rfl, trivial, trivial⟩
  obtain ⟨t, ht, htyped⟩ := (Mixed.Raw.source_wf sig sumSig hΓ hs strict p hp).toLetIter
  exact ⟨t, ht, cycleTyped, htyped, Mixed.repeatOnRight_not_raw sig sumSig rfl sumVisible hΓ hs strict p hp ht⟩

example : (returnEither (ss := slots)).visibleDepth (ε := Fx) = 1 := rfl

/-- A written product binder under an effectful case needs no raw mixed
representation to use the general written-language bound. -/
abbrev withProductBinder : Expr (Empty ⊕ Unit) :=
  .case (.op (.inr ()) .unit) (.let₂ (.pair (.var 0) (.var 0)) (.var 0)) (.var 0)

private theorem productBinderTyped : Wf Γ withProductBinder A strict :=
  .case (A := A) (B := A) (.op (f := Sum.inr ()) le_rfl (.unit _ _))
    (.let₂ (.pair (.var 0 bot_le) (.var 0 bot_le)) (.var 0 bot_le))
    (.var 0 bot_le)

example : ∃ t : Term Γ.length, withProductBinder.toLetIter Γ.length = some t ∧
    ¬ AbortEquiv (⊥ : Fx) free Γ.toBoundCtx cycle t A := by
  have hs : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0
  obtain ⟨t, ht, _⟩ := productBinderTyped.toLetIter
  exact ⟨t, ht, Mixed.repeatOnRight_not_written sig sumSig rfl sumVisible hs strict withProductBinder
    productBinderTyped ht⟩

abbrev modelSlots : Fin 1 → Unit := fun _ => ()

/-- The reply supplied by the free-tree valuation can be reused any finite
number of times along the right branch. -/
example : ∃ d : Derivation (Empty ⊕ Unit) free Γ.toBoundCtx cycle A,
    ∀ k, ITree.HasVisiblePrefix k
      (d.denote (Ty.denote (Atom sig modelSlots)) (SumCall.instructions (ε := Fx) sig sumSig modelSlots)
        (fun x => x.elim) (fun i => i.elim0)) :=
  Mixed.repeatOnRight_hasVisiblePrefixes sig sumSig rfl modelSlots (fun i => i.elim0) (.var 0)

end LetIterCyclicFixture

namespace LetIterWrittenMixedFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev sig : Signature Unit Bool := ⟨fun _ => 1, fun _ _ => (), fun _ => ()⟩
abbrev sumSig : SumCall.SumSignature Unit Unit :=
  ⟨fun _ => 0, fun _ i => i.elim0, fun _ => (), fun _ => ()⟩
abbrev A : Ty Unit := .base ()
abbrev Γ : EffectCtx (Ty Unit) Fx := []
abbrev free := (Ctx.nil : Ctx Empty (Ty Unit))
abbrev slots : Fin Γ.length → Unit := Fin.elim0
abbrev Ops := Bool ⊕ Unit

local instance : HasEff Bool Fx := ⟨fun _ => strict⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff Ops Fx := SumCall.effects
local instance : HasTy Ops (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

private theorem visibleAtom (f : Bool) : ¬ IsPure (⊥ : Fx) f := by
  change strict ≠ (⊥ : Fx)
  decide

private theorem visibleSum (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

abbrev usePayload (tag : Bool) : Expr Ops := .op (.inl tag) (.pair (.var 0) .unit)

/-- The sum request's response survives both an ordinary let and a product
binder before the case selects which visible atomic request receives it. -/
abbrev expression : Expr Ops :=
  .let₁ (.pair (.op (.inr ()) .unit) .unit)
    (.let₂ (.var 0) (.case (.var 1) (usePayload false) (usePayload true)))

private theorem expressionTyped : Wf Γ expression A strict :=
  .let₁ (.pair (.op (f := Sum.inr ()) le_rfl (.unit _ _)) (.unit _ _))
    (.let₂ (.var 0 bot_le)
      (.case (.var 1 bot_le)
        (.op (f := Sum.inl false) le_rfl (.pair (.var 0 bot_le) (.unit _ _)))
        (.op (f := Sum.inl true) le_rfl (.pair (.var 0 bot_le) (.unit _ _)))))

abbrev native : Tm Empty Ops Γ.length :=
  .let₁ (.pair (.op (.inr ()) .unit) .unit)
    (.let₂ (.bv 0) (.case (.bv 1)
      (.op (.inl false) (.pair (.bv 0) .unit))
      (.op (.inl true) (.pair (.bv 0) .unit))))

private theorem lowers : expression.toLetIter Γ.length = some native := rfl

def derivation : Derivation Ops free Γ.toBoundCtx native A :=
  .let₁ (.pair (.op (f := Sum.inr ()) .unit) .unit)
    (.let₂ .bv (.case .bv
      (.op (f := Sum.inl false) (.pair .bv .unit))
      (.op (f := Sum.inl true) (.pair .bv .unit))))

abbrev expected : Mixed.Program sig sumSig () slots :=
  .sum () (fun i => i.elim0)
    (.atom false (fun _ => .var 0) (.ret (.var 0)))
    (.atom true (fun _ => .var 0) (.ret (.var 0)))

private theorem expectedTyped : expected.WellTyped sig sumSig strict :=
  ⟨fun i => i.elim0, le_rfl,
    ⟨fun _ => trivial, visibleAtom false, le_rfl, trivial⟩,
    ⟨fun _ => trivial, visibleAtom true, le_rfl, trivial⟩⟩

private theorem ctxPure : Γ.Pure := fun i => i.elim0
private theorem slotsTyped : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0

variable {m : Nat} (ms : Fin m → Unit)

local notation "D" => Ty.denote (Atom sig ms)
local notation "M" => SumCall.instructions (ε := Fx) sig sumSig ms
local notation "emptyEnv" => (fun x : Empty => x.elim)

private theorem evalAtom (f : Bool) (r : Atom sig ms ()) :
    (M).eval (.inl f) (r, PUnit.unit) =
      ITree.vis (.atom f (fun _ => r.down)) (fun reply => ITree.ret ⟨reply⟩) := by
  change (M).eval (.inl f) (packArgs sig ms 1 (sig.arg f) (fun _ => r.down)) = _
  simp only [SumCall.instructions, ite_eq_right (visibleAtom f), readArgs, unpackArgs_packArgs]

private theorem evalSum :
    (M).eval (.inr ()) PUnit.unit =
      ITree.vis (.sum () (fun j => j.elim0))
        (fun r => ITree.ret (SumCall.responseValue sig sumSig ms r)) := by
  change (M).eval (.inr ()) (packArgs sig ms 0 (sumSig.arg ()) (fun j => j.elim0)) = _
  simp only [SumCall.instructions, unpackArgs_packArgs]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem expressionDenote (vars : (i : Fin Γ.length) → Tree sig ms (slots i)) :
    derivation.denote D M emptyEnv (variableEnv sig ms slotsTyped vars) =
      expected.denote sig sumSig ms vars := by
  simp only [derivation, Derivation.denote, pure_bind]
  erw [evalSum ms, ITree.vis_bind, ITree.vis_bind]
  simp only [Mixed.Program.denote]
  congr 1
  · congr 1
    funext i
    exact i.elim0
  funext reply
  erw [pure_bind]
  cases reply with
  | inl r =>
    erw [pure_bind]
    exact evalAtom ms false ⟨r⟩
  | inr r =>
    erw [pure_bind]
    exact evalAtom ms true ⟨r⟩

private theorem agreesWithExpected : Eqv Γ A strict expression expected.source := by
  obtain ⟨p, hp, he⟩ := Mixed.Written.normalize_atomic sig sumSig ctxPure slotsTyped strict expressionTyped
  have eq : p = expected := by
    apply Mixed.eq_of_denote_eq sig sumSig
    intro m ms vars
    obtain ⟨dp, hdp⟩ := Mixed.eval_exists sig sumSig ms slotsTyped strict p hp
    have hn := he.toLetIter lowers (Mixed.lowers sig sumSig p)
    have agree := denote_eq_of_abortEquiv_nil.{0, 2, 0, 0} (Atom sig ms)
      (SumCall.instructions (ε := Fx) sig sumSig ms)
      (Mixed.instructions_respectsPure sig sumSig ms visibleSum) hn derivation dp
      (variableEnv sig ms slotsTyped vars)
    exact (hdp vars).symm.trans (agree.symm.trans (expressionDenote ms vars))
  exact eq ▸ he

example : AbortEquiv (⊥ : Fx) free Γ.toBoundCtx native expected.native A ∧
    Eqv Γ A strict expression expected.source := by
  have hreflect := Mixed.Written.endpoint_reflection sig sumSig visibleSum ctxPure slotsTyped strict expressionTyped
    (Mixed.source_wf sig sumSig ctxPure slotsTyped strict expected expectedTyped)
    lowers (Mixed.lowers sig sumSig expected)
  exact ⟨hreflect.mpr agreesWithExpected, hreflect.mp (hreflect.mpr agreesWithExpected)⟩

end LetIterWrittenMixedFixture

namespace LetIterStructuredResultFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open LetIterWrittenMixedFixture

local instance : HasEff Bool Fx := ⟨fun _ => strict⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff Ops Fx := SumCall.effects
local instance : HasTy Ops (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev Choice : Ty Unit := .coprod A A
abbrev Result : Ty Unit := .product Choice .unit
abbrev req : Expr Ops := .op (.inr ()) .unit
abbrev body : Expr Ops := .pair (.var 0) .unit
abbrev expression : Expr Ops := .let₁ req body

private theorem reqTyped : Wf Γ req Choice strict :=
  .op (f := Sum.inr ()) le_rfl (.unit _ _)

private theorem expressionTyped : Wf Γ expression Result strict :=
  .let₁ reqTyped (.pair (.var 0 bot_le) (.unit _ _))

abbrev native : Tm Empty Ops Γ.length :=
  .let₁ (.op (.inr ()) .unit) (.pair (.bv 0) .unit)

private theorem lowers : expression.toLetIter Γ.length = some native := rfl

/-- Both branches return a product with the response sum still tagged. -/
abbrev expected : Mixed.Written.Code sig sumSig Result slots :=
  .sum () (fun i => i.elim0)
    (.ret (.pair (.inl (.tree (.var 0))) .unit))
    (.ret (.pair (.inr (.tree (.var 0))) .unit))

abbrev swappedLeft : Mixed.Written.Code sig sumSig Result slots :=
  .sum () (fun i => i.elim0)
    (.ret (.pair (.inr (.tree (.var 0))) .unit))
    (.ret (.pair (.inr (.tree (.var 0))) .unit))

private theorem expectedTyped : expected.WellTyped sig sumSig strict :=
  ⟨fun i => i.elim0, le_rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

private theorem swappedTyped : swappedLeft.WellTyped sig sumSig strict :=
  ⟨fun i => i.elim0, le_rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

private theorem agrees : Eqv Γ Result strict expression expected.source := by
  have hL : Wf [(A, ⊥)] (.inl (.var 0) : Expr Ops) Choice (⊥ : Fx) := .inl (.var 0 le_rfl)
  have hR : Wf [(A, ⊥)] (.inr (.var 0) : Expr Ops) Choice (⊥ : Fx) := .inr (.var 0 le_rfl)
  have hl := hL.weakenEffect (bot_le : (⊥ : Fx) ≤ strict)
  have hr := hR.weakenEffect (bot_le : (⊥ : Fx) ≤ strict)
  have hc := Wf.case reqTyped hl hr
  have hb : Wf [(Choice, ⊥)] body Result strict := .pair (.var 0 bot_le) (.unit _ _)
  have hw : Wf [(Choice, ⊥), (A, ⊥)] body.wk1 Result strict := .pair (.var 0 bot_le) (.unit _ _)
  have eta := (Eqv.step (Step.rewrite hc reqTyped (.case_eta _))).symm
  have push := Eqv.step (Step.rewrite (.let₁ hc hb)
    (.case reqTyped (.let₁ hl hw) (.let₁ hr hw)) (.let1_case _ _ _ _))
  exact (Eqv.let1 eta (.refl hb)).trans
    (push.trans (.case (.refl reqTyped) (.step (.let1_beta hL hw)) (.step (.let1_beta hR hw))))

/-- Run the public reflection theorem at the original strict bound instead
of identifying the compound result with an atomic code. -/
example : AbortEquiv (⊥ : Fx) free Γ.toBoundCtx native expected.native Result ∧
    Eqv Γ Result strict expression expected.source := by
  have h := Mixed.Written.endpoint_reflection_structured sig sumSig visibleSum ctxPure slotsTyped strict
    expressionTyped agrees.endpoints_wf.2 lowers (Mixed.Written.Code.lowers sig sumSig expected)
  exact ⟨h.mpr agrees, h.mp (h.mpr agrees)⟩

/-- The very same requests with a changed injection inside the returned
product are distinguishable at their original bound. -/
example : ¬ Eqv Γ Result strict expected.source swappedLeft.source := by
  intro h
  have hn := h.toLetIter (Mixed.Written.Code.lowers sig sumSig expected)
    (Mixed.Written.Code.lowers sig sumSig swappedLeft)
  have hcode := Mixed.Written.Code.native_eq_implies_eq sig sumSig visibleSum slotsTyped strict
    expected swappedLeft expectedTyped swappedTyped hn
  simp [expected, swappedLeft] at hcode

abbrev requestThenUnit : Mixed.Written.Code sig sumSig .unit slots :=
  .sum () (fun i => i.elim0) (.ret .unit) (.ret .unit)

abbrev returnUnit : Mixed.Written.Code sig sumSig .unit slots := .ret .unit

/-- Unit compares equal at a pure return. It does not erase the preceding request. -/
example : ¬ AbortEquiv (⊥ : Fx) free Γ.toBoundCtx requestThenUnit.native returnUnit.native .unit := by
  intro h
  have hcode := Mixed.Written.Code.native_eq_implies_eq sig sumSig visibleSum slotsTyped strict
    requestThenUnit returnUnit ⟨fun i => i.elim0, le_rfl, trivial, trivial⟩ trivial h
  cases hcode

end LetIterStructuredResultFixture

namespace LetIterStructuredInputFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open LetIterWrittenMixedFixture (Fx strict sig sumSig A Ops free visibleSum)

local instance : HasEff Bool Fx := ⟨fun _ => strict⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff Ops Fx := SumCall.effects
local instance : HasTy Ops (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev Choice : Ty Unit := .coprod A A
abbrev Held : Ty Unit := .product Choice .unit
abbrev Γ : EffectCtx (Ty Unit) Fx := [(A, ⊥), (Held, ⊥)]

private theorem ctxPure : Γ.Pure := by
  intro i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i

abbrev direct : Expr Ops := .case (.op (.inr ()) .unit) (.var 2) (.var 2)
abbrev rebuiltArm : Expr Ops := .let₂ (.var 2) (.pair (.var 1) (.var 0))
abbrev rebuilt : Expr Ops := .case (.op (.inr ()) .unit) rebuiltArm rebuiltArm

private theorem requestTyped : Wf Γ (.op (Sum.inr ()) .unit : Expr Ops) Choice strict :=
  .op (f := Sum.inr ()) le_rfl (.unit _ _)

private theorem directTyped : Wf Γ direct Held strict :=
  .case (A := A) (B := A) requestTyped (.var 2 bot_le) (.var 2 bot_le)

private theorem rebuiltTyped : Wf Γ rebuilt Held strict := by
  have arm : Wf ((A, ⊥) :: Γ) rebuiltArm Held strict :=
    .let₂ (.var 2 bot_le) (.pair (.var 1 bot_le) (.var 0 bot_le))
  exact .case (A := A) (B := A) requestTyped arm arm

abbrev directNative : Tm Empty Ops Γ.length :=
  .case (.op (.inr ()) .unit) (.bv 2) (.bv 2)
abbrev rebuiltNativeArm : Tm Empty Ops (Γ.length + 1) :=
  .let₂ (.bv 2) (.pair (.bv 1) (.bv 0))
abbrev rebuiltNative : Tm Empty Ops Γ.length :=
  .case (.op (.inr ()) .unit) rebuiltNativeArm rebuiltNativeArm

/-- The case performs a visible request and preserves a non-head input
product containing a sum. Native pair eta rebuilds the product in both arms. -/
example : Eqv Γ Held strict direct rebuilt := by
  have request : HasType Ops free Γ.toBoundCtx (.op (Sum.inr ()) .unit) Choice :=
    .op (f := Sum.inr ()) .unit
  have retained : HasType Ops free (.snoc Γ.toBoundCtx A) (.bv 2) Held := .bv
  have eta := Silmaril.Isotope.LetIter.LocallyNameless.Equiv.pairEta (pureEff := (⊥ : Fx)) retained
  have hn : AbortEquiv (⊥ : Fx) free Γ.toBoundCtx directNative rebuiltNative Held :=
    .equiv (.case (.refl request) eta.symm eta.symm)
  exact (Mixed.Written.endpoint_reflection_all_contexts sig sumSig visibleSum ctxPure strict
    directTyped rebuiltTyped rfl rfl).mp hn

end LetIterStructuredInputFixture

namespace LetIterStructuredReplyFixture

open Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured

set_option backward.isDefEq.respectTransparency false

private inductive Instr
  | stop | split | sendL | sendR | pureBit
  deriving DecidableEq

private def atom : Ty Unit := .base ()
private def payload : Ty Unit := .product (.coprod atom atom) .unit

private instance : HasTy Instr (Ty Unit) where
  src
    | .stop | .split | .pureBit => .unit
    | .sendL | .sendR => atom
  trg
    | .stop => .empty
    | .split => payload
    | .pureBit => atom
    | .sendL | .sendR => .unit

private instance : HasEff Instr Bool where
  eff f := f != .pureBit

private def V : Unit → Type := fun _ => Bool

private def P : PureMaps (Φ := Instr) (ε := Bool) V :=
  fun f hf => by
    cases f
    case pureBit => exact fun _ => true
    all_goals cases hf

private theorem stop_visible : ¬ IsPure (⊥ : Bool) Instr.stop := by
  change true ≠ false
  decide
private theorem split_visible : ¬ IsPure (⊥ : Bool) Instr.split := by
  change true ≠ false
  decide
private theorem left_visible : ¬ IsPure (⊥ : Bool) Instr.sendL := by
  change true ≠ false
  decide

private abbrev Γ₀ := (Ctx.nil : Ctx Empty (Ty Unit))
private abbrev β₀ := (BoundCtx.nil : BoundCtx (Ty Unit) 0)
private abbrev D := Ty.denote (Lifted V)
private abbrev noVars : BoundEnv D β₀ := fun i => i.elim0
private noncomputable abbrev M := instructions V P

private def halt : Tm Empty Instr 0 :=
  .let₁ (.op .stop .unit) (.abort (.bv 0))

private def haltTyping : Derivation Instr Γ₀ β₀ halt (.unit : Ty Unit) :=
  .let₁ (.op .unit) (.abort (.bv (ι := 0)))

-- Empty response means the continuation has no possible entry. The request
-- from the actual native program remains observable.
example : headRequest V (haltTyping.denote D M (fun x => x.elim) noVars) =
    Part.some (some ⟨Instr.stop, PUnit.unit⟩) := by
  unfold haltTyping
  rw [denote_letOp_of_not_pure V P stop_visible]
  simp only [Derivation.denote, pure_bind]
  exact head_of_vis V _ _ _

private def continuation : Tm Empty Instr 1 :=
  .let₂ (.bv 0)
    (.case (.bv 1) (.op .sendL (.bv 0)) (.op .sendR (.bv 0)))

private def continuationTyping :
    Derivation Instr Γ₀ (β₀.snoc payload) continuation (.unit : Ty Unit) :=
  .let₂ (.bv (ι := 0)) (.case (.bv (ι := 1))
    (.op (.bv (ι := 0))) (.op (.bv (ι := 0))))

private def call : Tm Empty Instr 0 := .let₁ (.op .split .unit) continuation

private def callTyping : Derivation Instr Γ₀ β₀ call (.unit : Ty Unit) :=
  .let₁ (.op .unit) continuationTyping

private def leftSlots : Fin (1 + 0) → Unit := Fin.addCases (fun _ => ()) Fin.elim0
private def leftShape : ReplyShape leftSlots payload :=
  .pair (.inl (.atom ())) .unit
private def leftValues (_ : Fin (1 + 0)) : Bool := true

-- The test reply really is source syntax at bottom, with one fresh atomic slot.
example : Wf ([(atom, false)] : EffectCtx (Ty Unit) Bool)
    (leftShape.source (Φ := Instr) id) payload (⊥ : Bool) :=
  ReplyShape.wf leftShape (Γ := [(atom, false)]) id (by
    intro i
    exact Fin.cases (motive := fun j => ([(atom, false)] : EffectCtx (Ty Unit) Bool).get j =
      (.base (leftSlots j), (⊥ : Bool))) rfl (fun j => j.elim0) i)

private noncomputable def next
    (reply : Ty.denote V payload) : ITree.Tree (Event (Φ := Instr) V) (D (.unit : Ty Unit)) :=
  continuationTyping.denote D M (fun x => x.elim)
    (noVars.snoc ((toSmall V payload).symm reply))

-- The actual native call emits only the outer request before any reply.
example : callTyping.denote D M (fun x => x.elim) noVars =
    ITree.vis (.call Instr.split PUnit.unit) next := by
  unfold callTyping
  rw [denote_letOp_of_not_pure V P split_visible]
  simp only [Derivation.denote, pure_bind]
  rfl

-- Testing the left constructor under true reaches the distinct left
-- request and passes the very payload field selected by that shape.
example : headRequest V (next (leftShape.denote V leftValues)) =
    Part.some (some ⟨Instr.sendL, true⟩) := by
  unfold next continuationTyping
  simp only [Derivation.denote, pure_bind, BoundEnv.snoc_zero]
  change headRequest V ((M.eval Instr.sendL ⟨true⟩)) = _
  rw [show M.eval Instr.sendL ⟨true⟩ = ITree.vis (.call Instr.sendL true) (fun _ => ITree.ret PUnit.unit) by
    classical
    simp only [M, instructions, left_visible, dite_false]
    rfl]
  exact head_of_vis V _ _ _

end LetIterStructuredReplyFixture

namespace LetIterStructuredPureValuesFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

set_option backward.isDefEq.respectTransparency false

private inductive Inst where
  | collect | seal | halt | note

private abbrev Eff := Bool × Bool
private abbrev bound : Eff := (true, false)
private abbrev argument : Ty Unit := .coprod (.base ()) .unit
private abbrev collectInput : Ty Unit := .product (Ty.coprod .unit .unit) .unit

private instance : HasTy Inst (Ty Unit) where
  src
    | .collect => collectInput
    | .halt => argument
    | _ => .unit
  trg
    | .collect => .base ()
    | .halt => .empty
    | _ => .unit

private instance : HasEff Inst Eff where
  eff
    | .collect | .seal => ⊥
    | _ => bound

local instance : EffectIteration Eff := EffectIteration.complete Eff

private def profile : Profile (α := Unit) Inst Eff :=
  fun f hf => by
    cases f
    · exact .atom () rfl
    · exact .unit rfl
    all_goals cases hf

private abbrev Γ := ([] : EffectCtx (Ty Unit) Eff)
private abbrev Γ₀ := (Ctx.nil : Ctx Empty (Ty Unit))
private abbrev β := EffectCtx.toBoundCtx Γ
private abbrev sorts : Fin Γ.length → Unit := fun _ => ()
private theorem pureCtx : EffectCtx.Pure Γ := fun i => i.elim0
private theorem ctxSorts : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (sorts i) := fun i => i.elim0
private theorem halt_nonpure : ¬ IsPure (⊥ : Eff) Inst.halt := fun h => Bool.noConfusion (congrArg Prod.fst h)

private abbrev a : Expr Inst :=
  .inl (.op .collect (.pair (.inl .unit) (.op .seal .unit)))
private abbrev b : Expr Inst :=
  .inl (.op .collect (.pair (.inl .unit) .unit))
private abbrev k : Expr Inst := .op .note .unit
private abbrev l : Expr Inst := .unit
private abbrev u : Tm Empty Inst 0 :=
  .inl (.op .collect (.pair (.inl .unit) (.op .seal .unit)))
private abbrev v : Tm Empty Inst 0 := .inl (.op .collect (.pair (.inl .unit) .unit))
private abbrev t : Tm Empty Inst 1 := .op .note .unit
private abbrev s : Tm Empty Inst 1 := .unit

private theorem a_typed : Wf Γ a (instrSrc Inst.halt) (⊥ : Eff) :=
  .inl (.op le_rfl (.pair (.inl (.unit _ _)) (.op le_rfl (.unit _ _))))
private theorem b_typed : Wf Γ b (instrSrc Inst.halt) (⊥ : Eff) :=
  .inl (.op le_rfl (.pair (.inl (.unit _ _)) (.unit _ _)))

private theorem k_typed : Wf ((Ty.empty, (⊥ : Eff)) :: Γ) k (.unit : Ty Unit) bound :=
  .op (f := Inst.note) le_rfl (.unit _ _)

private theorem l_typed : Wf ((Ty.empty, (⊥ : Eff)) :: Γ) l (.unit : Ty Unit) bound :=
  .unit _ _

example : bound < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

-- The unit-returning primitive in the raw argument and the arbitrary
-- effectful continuation are handled at the supplied strict bound.
example :
    AbortEquiv (⊥ : Eff) Γ₀ β (.let₁ (.op Inst.halt u) t) (.let₁ (.op Inst.halt v) s) (.unit : Ty Unit) ↔
      Eqv Γ (.unit : Ty Unit) bound (.let₁ (.op Inst.halt a) k) (.let₁ (.op Inst.halt b) l) :=
  empty_reply_constructor_reflection (slots := sorts) profile pureCtx ctxSorts halt_nonpure halt_nonpure
    rfl le_rfl le_rfl a_typed b_typed (.inl (.op (.pair (.inl .unit) (.op .unit))))
    (.inl (.op (.pair (.inl .unit) .unit))) k_typed l_typed rfl rfl rfl rfl

private abbrev leftValue : Value (Φ := Inst) (ε := Eff) sorts argument :=
  .inl (Value.op Inst.collect (show IsPure (⊥ : Eff) Inst.collect from rfl) (a := ()) rfl
    (.pair (.inl .unit) .unit))

private abbrev rightValue : Value (Φ := Inst) (ε := Eff) sorts argument :=
  .inl (Value.op Inst.collect (show IsPure (⊥ : Eff) Inst.collect from rfl) (a := ()) rfl
    (.pair (.inr .unit) .unit))

-- Changing just the tag inside the argument of a pure generator changes
-- the outer visible request, even though neither call can reply.
example :
    ¬ AbortEquiv (⊥ : Eff) Γ₀ β
      (.let₁ (.op Inst.halt leftValue.native) .unit)
      (.let₁ (.op Inst.halt rightValue.native) .unit) (.unit : Ty Unit) := by
  intro h
  have req := request_eq_of_abortEquiv profile (fun i => i.elim0)
    halt_nonpure halt_nonpure .unit .unit h
  have args : leftValue = rightValue := eq_of_heq (Sigma.mk.inj req).2
  have differ := congrArg Value.source args
  cases differ

end LetIterStructuredPureValuesFixture

namespace LetIterStructuredAtomicRepliesFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured (headRequest head_of_vis)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues
  (Atom Value Profile ConstructorLeaf)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence

set_option backward.isDefEq.respectTransparency false

private inductive Instruction
  | ask | send | stamp | unitOp

private abbrev Eff := Bool × Bool
private abbrev bound : Eff := (true, false)
private abbrev A : Ty Unit := .base ()

private instance : HasTy Instruction (Ty Unit) where
  src
    | .send => .product A .unit
    | .stamp => A
    | _ => .unit
  trg
    | .unitOp => .unit
    | _ => A

private instance : HasEff Instruction Eff where
  eff
    | .stamp | .unitOp => ⊥
    | _ => bound

local instance : EffectIteration Eff := EffectIteration.complete Eff

private def profile : Profile (α := Unit) Instruction Eff :=
  fun f hf => by
    cases f
    case stamp => exact .atom () rfl
    case unitOp => exact .unit rfl
    all_goals cases hf

private theorem askVisible : ¬ IsPure (⊥ : Eff) Instruction.ask :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private theorem sendVisible : ¬ IsPure (⊥ : Eff) Instruction.send :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private abbrev Γ := ([] : EffectCtx (Ty Unit) Eff)
private abbrev Γ' := (A, (⊥ : Eff)) :: Γ
private abbrev β := EffectCtx.toBoundCtx Γ
private abbrev Γ₀ := (Ctx.nil : Ctx Empty (Ty Unit))
private abbrev sorts : Fin 0 → Unit := Fin.elim0
private abbrev freshSorts : Fin 1 → Unit := Fin.cases () sorts

private theorem pureCtx : EffectCtx.Pure Γ := fun i => i.elim0
private theorem sourceSlots : ∀ i : Fin Γ.length, (Γ.get i).1 = Ty.base (sorts i) := fun i => i.elim0
private theorem nativeSlots : ∀ i : Fin 0, β.get i = Ty.base (sorts i) := fun i => i.elim0
private theorem nextSlots : ∀ i : Fin 1, (β.snoc A).get i = Ty.base (freshSorts i) :=
  replySlots nativeSlots rfl

private abbrev rawTail : Expr Instruction :=
  .let₁ (.op .send (.pair (.var 0) .unit)) (.var 0)

private abbrev raw : Expr Instruction :=
  .let₁ (.op .ask (.op .unitOp .unit)) rawTail

private abbrev clean : Expr Instruction :=
  .let₁ (.op .ask .unit) rawTail

private theorem tailWritten : Written A bound Γ' rawTail :=
  .call (f := Instruction.send) sendVisible rfl
    (.pair (.var 0 bot_le) (.unit _ _)) (.pair (.var 0) .unit) le_rfl
    (.ret (.var 0 bot_le) (.var 0))

private theorem rawWritten : Written A bound Γ raw :=
  .call (f := Instruction.ask) askVisible rfl (.op (f := Instruction.unitOp) le_rfl (.unit _ _))
    (.op .unit) le_rfl tailWritten

private theorem cleanWritten : Written A bound Γ clean :=
  .call (f := Instruction.ask) askVisible rfl (.unit _ _) .unit le_rfl tailWritten

private abbrev loweredTail : Tm Empty Instruction 1 :=
  .let₁ (.op .send (.pair (.bv 0) .unit)) (.bv 0)

example : bound < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

-- Written reflection normalizes the pure unit-result operation at the
-- supplied bound. The second request passes the first reply as a field.
example :
    AbortEquiv (⊥ : Eff) Γ₀ β
      (.let₁ (.op .ask (.op .unitOp .unit)) loweredTail)
      (.let₁ (.op .ask .unit) loweredTail) A ↔
    Eqv Γ A bound raw clean :=
  written_reflection profile pureCtx sourceSlots rawWritten cleanWritten rfl rfl

private abbrev forwardReply : Program (Φ := Instruction) (ε := Eff) A freshSorts :=
  .call Instruction.send sendVisible rfl (.pair (.var 0) .unit) (.ret (.var 0))

private abbrev stampReply : Program (Φ := Instruction) (ε := Eff) A freshSorts :=
  .call Instruction.send sendVisible rfl
    (.pair (.op Instruction.stamp (show IsPure (⊥ : Eff) Instruction.stamp from rfl) rfl (.var 0)) .unit)
    (.ret (.var 0))

private abbrev forward : Program (Φ := Instruction) (ε := Eff) A sorts :=
  .call Instruction.ask askVisible rfl .unit forwardReply

private abbrev stamped : Program (Φ := Instruction) (ε := Eff) A sorts :=
  .call Instruction.ask askVisible rfl .unit stampReply

-- At the canonical valuation in the scope extended by the atomic reply,
-- the generic atom itself occurs in the second visible request.
example :
    headRequest (Atom (Φ := Instruction) (ε := Eff) freshSorts)
      (forwardReply.denote profile freshSorts nextSlots Value.var) =
      Part.some (some ⟨Instruction.send, (Value.var 0, PUnit.unit)⟩) := by
  rw [denote_call]
  exact head_of_vis _ _ _ _

-- Both programs make the same first request and both use its reply in the
-- next request. Passing the fresh atom and applying a pure generator to it
-- lead to distinguishable visible inputs.
example : ¬ AbortEquiv (⊥ : Eff) Γ₀ β forward.native stamped.native A := by
  intro h
  have eq := eq_of_abortEquiv profile nativeSlots h
  have src := congrArg Program.source eq
  cases src

end LetIterStructuredAtomicRepliesFixture

namespace LetIterStructuredProductRepliesFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
  (Event ReplyShape headRequest head_of_vis)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues
  (Atom Value Profile)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence

set_option backward.isDefEq.respectTransparency false

private inductive Instruction
  | receive | publish | choose

private abbrev Eff := Bool × Bool
private abbrev bound : Eff := (true, false)
private abbrev A : Ty Unit := .base ()
private abbrev P : Ty Unit := .product A A
private abbrev S : Ty Unit := .coprod A A

private instance : HasTy Instruction (Ty Unit) where
  src
    | .receive => .unit
    | .publish | .choose => P
  trg
    | .receive => P
    | .publish => A
    | .choose => S

private instance : HasEff Instruction Eff where
  eff _ := bound

local instance : EffectIteration Eff := EffectIteration.complete Eff

private theorem visible (f : Instruction) : ¬ IsPure (⊥ : Eff) f :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private def profile : Profile (α := Unit) Instruction Eff :=
  fun f hf => (visible f hf).elim

private abbrev Γ : EffectCtx (Ty Unit) Eff := [(A, ⊥)]
private abbrev fields := (A, (⊥ : Eff)) :: (A, ⊥) :: Γ
private abbrev β := Γ.toBoundCtx
private abbrev Γ₀ := (Ctx.nil : Ctx Empty (Ty Unit))
private abbrev sorts : Fin Γ.length → Unit := fun _ => ()
private abbrev freshSorts := pairSlots () () sorts

private theorem pureCtx : Γ.Pure := fun i => Fin.cases rfl (fun i => i.elim0) i
private theorem sourceSlots : ∀ i : Fin Γ.length, (Γ.get i).1 = Ty.base (sorts i) :=
  fun i => Fin.cases rfl (fun i => i.elim0) i
private theorem nativeSlots : ∀ i : Fin Γ.length, β.get i = Ty.base (sorts i) :=
  fun i => Fin.cases rfl (fun i => i.elim0) i

private abbrev tail (swap : Bool) : Expr Instruction :=
  let arg := if swap then Expr.pair (.var 0) (.var 1) else Expr.pair (.var 1) (.var 0)
  .let₁ (.op .publish arg) (.var 3)

private abbrev direct (swap : Bool) : Expr Instruction :=
  .let₂ (.op .receive .unit) (tail swap)

private abbrev factored (swap : Bool) : Expr Instruction :=
  .let₁ (.op .receive .unit) (.let₂ (.var 0) (tail swap).wk2)

private theorem tailWritten (swap : Bool) : Written A bound fields (tail swap) := by
  cases swap
  · exact .call (f := Instruction.publish) (visible _) rfl (.pair (.var 1 bot_le) (.var 0 bot_le))
      (.pair (.var 1) (.var 0)) le_rfl (.ret (.var 3 bot_le) (.var 3))
  · exact .call (f := Instruction.publish) (visible _) rfl (.pair (.var 0 bot_le) (.var 1 bot_le))
      (.pair (.var 0) (.var 1)) le_rfl (.ret (.var 3 bot_le) (.var 3))

private theorem directWritten (swap : Bool) : Written A bound Γ (direct swap) :=
  .callPair (f := Instruction.receive) (visible _) rfl (.unit _ _) .unit le_rfl (tailWritten swap)

private theorem factoredWritten (swap : Bool) : Written A bound Γ (factored swap) :=
  .callPairViaLet (f := Instruction.receive) (visible _) rfl (.unit _ _) .unit le_rfl (tailWritten swap)

private def continuation (swap : Bool) : Program (Φ := Instruction) (ε := Eff) A freshSorts :=
  .call Instruction.publish (visible _) rfl
    (if swap then .pair (.var 0) (.var 1) else .pair (.var 1) (.var 0)) (.ret (.var 3))

private def program (swap : Bool) : Program (Φ := Instruction) (ε := Eff) A sorts :=
  .callPair Instruction.receive (visible _) rfl .unit (continuation swap)

private abbrev canonical (swap : Bool) : Tm Empty Instruction Γ.length :=
  .let₂ (.op .receive .unit)
    (.let₁ (.op .publish (if swap then .pair (.bv 0) (.bv 1) else .pair (.bv 1) (.bv 0))) (.bv 3))

private abbrev nested : Tm Empty Instruction Γ.length :=
  .let₁ (.op .receive .unit) (.let₂ (.bv 0) (.let₁ (.op .publish (.pair (.bv 1) (.bv 0))) (.bv 4)))

example : bound < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

-- The field slots are different free generators, even at the same sort.
example : (Value.var (Φ := Instruction) (ε := Eff) (slots := freshSorts) 1) ≠ Value.var 0 := by
  intro h
  cases h

-- Observing the receive node at the ordered constructor reply installs the
-- two distinct fresh slots before publish. The old slot is retained at 2.
example :
    let V := Atom (Φ := Instruction) (ε := Eff) freshSorts
    let shape := ReplyShape.pair (ReplyShape.atom ()) (ReplyShape.atom ())
    let reply := shape.denote V
      (Fin.addCases (motive := fun _ => V ()) (fun _ => Value.var 1) (fun _ => Value.var 0))
    ∃ k : Ty.denote V P → ITree.Tree (Event (Φ := Instruction) V) _,
      (program false).denote profile freshSorts nativeSlots (fun _ => Value.var 2) =
        ITree.vis (.call Instruction.receive PUnit.unit) k ∧
      headRequest V (k reply) = Part.some (some ⟨Instruction.publish, (Value.var 1, Value.var 0)⟩) := by
  dsimp only
  rw [program, denote_callPair]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  rw [continuation, denote_call]
  exact head_of_vis _ _ _ _

private theorem tailWf : Wf fields (tail false) A bound :=
  .let₁ (.op (f := Instruction.publish) le_rfl (.pair (.var 1 bot_le) (.var 0 bot_le)))
    (.var 3 bot_le)

-- The whole reply can be reconstructed as the pair of fields. Checked
-- source substitution and beta recover the body, including the old slot.
example :
    Eqv fields A bound (ProductSplit.split 0 (.let₂ (.var 0) (tail false).wk2)) (tail false) :=
  pairLet_specialize tailWf

example : Eqv Γ A bound (direct false) (factored false) :=
  pairLet_bind (.op (f := Instruction.receive) le_rfl (.unit _ _)) tailWf

example :
    AbortEquiv (⊥ : Eff) Γ₀ β (canonical false) nested A ↔
      Eqv Γ A bound (direct false) (factored false) :=
  written_reflection profile pureCtx sourceSlots (directWritten false) (factoredWritten false) rfl rfl

private theorem distinct : ¬ AbortEquiv (⊥ : Eff) Γ₀ β (canonical false) (canonical true) A := by
  intro h
  have eq : program false = program true := eq_of_abortEquiv profile nativeSlots h
  have src := congrArg Program.source eq
  cases src

example : ¬ Eqv Γ A bound (direct false) (direct true) := by
  intro h
  exact distinct ((written_reflection profile pureCtx sourceSlots
    (directWritten false) (directWritten true) rfl rfl).mpr h)


private abbrev branchCtx := (A, (⊥ : Eff)) :: fields

private abbrev sumArm (swap : Bool) : Expr Instruction :=
  let arg := if swap then Expr.pair (.var 2) (.var 0) else Expr.pair (.var 0) (.var 2)
  .let₁ (.op .publish arg) (.var 4)

private theorem armWritten (swap : Bool) : Written A bound branchCtx (sumArm swap) := by
  cases swap
  · exact .call (f := Instruction.publish) (visible _) rfl (.pair (.var 0 bot_le) (.var 2 bot_le))
      (.pair (.var 0) (.var 2)) le_rfl (.ret (.var 4 bot_le) (.var 4))
  · exact .call (f := Instruction.publish) (visible _) rfl (.pair (.var 2 bot_le) (.var 0 bot_le))
      (.pair (.var 2) (.var 0)) le_rfl (.ret (.var 4 bot_le) (.var 4))

private abbrev chooseExpr : Expr Instruction := .op .choose (.pair (.var 1) (.var 0))

private abbrev mixedSource (swapRight : Bool) : Expr Instruction :=
  .let₂ (.op .receive .unit) (.case chooseExpr (sumArm false) (sumArm swapRight))

private abbrev mixedFactored (swapRight : Bool) : Expr Instruction :=
  .let₂ (.op .receive .unit) (.let₁ chooseExpr (.case (.var 0) (sumArm false).wk1 (sumArm swapRight).wk1))

private theorem mixedWritten (swapRight : Bool) : Written A bound Γ (mixedSource swapRight) :=
  .callPair (f := Instruction.receive) (visible _) rfl (.unit _ _) .unit le_rfl
    (.callSum (f := Instruction.choose) (visible _) rfl (.pair (.var 1 bot_le) (.var 0 bot_le))
      (.pair (.var 1) (.var 0)) le_rfl (armWritten false) (armWritten swapRight))

private theorem mixedFactoredWritten (swapRight : Bool) : Written A bound Γ (mixedFactored swapRight) :=
  .callPair (f := Instruction.receive) (visible _) rfl (.unit _ _) .unit le_rfl
    (.callSumViaLet (f := Instruction.choose) (visible _) rfl (.pair (.var 1 bot_le) (.var 0 bot_le))
      (.pair (.var 1) (.var 0)) le_rfl (armWritten false) (armWritten swapRight))

private abbrev branchSorts : Fin (Γ.length + 3) → Unit := Fin.cases () freshSorts

private def armProgram (swap : Bool) : Program (Φ := Instruction) (ε := Eff) A branchSorts :=
  .call Instruction.publish (visible _) rfl
    (if swap then .pair (.var 2) (.var 0) else .pair (.var 0) (.var 2)) (.ret (.var 4))

private def mixedProgram (swapRight : Bool) : Program (Φ := Instruction) (ε := Eff) A sorts :=
  .callPair Instruction.receive (visible _) rfl .unit
    (.callSum Instruction.choose (visible _) rfl (.pair (.var 1) (.var 0))
      (armProgram false) (armProgram swapRight))

private abbrev mixedNested : Tm Empty Instruction Γ.length :=
  .let₂ (.op .receive .unit)
    (.let₁ (.op .choose (.pair (.bv 1) (.bv 0)))
      (.case (.bv 0) (.let₁ (.op .publish (.pair (.bv 0) (.bv 3))) (.bv 5))
        (.let₁ (.op .publish (.pair (.bv 0) (.bv 3))) (.bv 5))))

-- Both tested shapes make the sum request with the two earlier fields.
-- The right branch can distinguish the new payload from the retained left
-- field, even though the left branch is identical in the two programs.
example : ¬ AbortEquiv (⊥ : Eff) Γ₀ β (mixedProgram false).native (mixedProgram true).native A := by
  intro h
  have eq := eq_of_abortEquiv profile nativeSlots h
  have src := congrArg Program.source eq
  cases src

example :
    AbortEquiv (⊥ : Eff) Γ₀ β (mixedProgram false).native mixedNested A ↔
      Eqv Γ A bound (mixedSource false) (mixedFactored false) :=
  written_reflection profile pureCtx sourceSlots (mixedWritten false) (mixedFactoredWritten false) rfl rfl

end LetIterStructuredProductRepliesFixture

namespace LetIterRecursiveReplyFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection (ConstructorCover)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured (ReplyShape)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape

set_option backward.isDefEq.respectTransparency false

private abbrev X : Ty Unit := .base ()
private abbrev Eff := Bool × Bool
private abbrev bound : Eff := (true, false)

private inductive Instruction
  | receive (reply : Ty Unit)
  | publish (reply : Ty Unit)

private instance : HasTy Instruction (Ty Unit) where
  src
    | .receive _ => .unit
    | .publish r => .product r X
  trg
    | .receive r => r
    | .publish _ => X

private instance : HasEff Instruction Eff where
  eff _ := bound

local instance : EffectIteration Eff := EffectIteration.complete Eff

private abbrev Γ : EffectCtx (Ty Unit) Eff := [(X, ⊥)]
private abbrev context (R : Ty Unit) := (R, (⊥ : Eff)) :: Γ

private theorem pureCtx : Γ.Pure :=
  fun i => Fin.cases rfl (fun j => j.elim0) i

private theorem atomicCtx (i : Fin Γ.length) : ∃ a, (Γ.get i).1 = Ty.base a :=
  ⟨(), Fin.cases rfl (fun j => j.elim0) i⟩

private abbrev request (R : Ty Unit) : Expr Instruction := .op (.receive R) .unit

private abbrev publish (R : Ty Unit) : Expr Instruction :=
  .op (.publish R) (.pair (.var 0) (.var 1))

private abbrev rebind (R : Ty Unit) : Expr Instruction :=
  .let₁ (.var 0) (.op (.publish R) (.pair (.var 0) (.var 2)))

private theorem requestWf (R : Ty Unit) : Wf Γ (request R) R bound :=
  .op (f := Instruction.receive R) le_rfl (.unit _ _)

private theorem publishWf (R : Ty Unit) : Wf (context R) (publish R) X bound :=
  .op (f := Instruction.publish R) le_rfl (.pair (.var 0 bot_le) (.var 1 bot_le))

private theorem rebindWf (R : Ty Unit) : Wf (context R) (rebind R) X bound :=
  .let₁ (.var 0 bot_le) (.op (f := Instruction.publish R) le_rfl (.pair (.var 0 bot_le) (.var 2 bot_le)))

private theorem acrossReply (R : Ty Unit) :
    Eqv Γ X bound (.let₁ (request R) (rebind R)) (.let₁ (request R) (publish R)) := by
  apply eqv_let_of_specializations atomicCtx pureCtx (requestWf R) (rebindWf R) (publishWf R)
  intro n sorts shape
  have literal := shape.wf (Φ := Instruction) (fieldIndex sorts Γ) (get_fieldIndex (Γ := Γ))
  have ambient := Wf.var (Φ := Instruction) (Γ := (R, ⊥) :: fieldCtx sorts Γ)
    (ambientIndex sorts Γ 0).succ (e := bound) (by
      change ((fieldCtx sorts Γ).get (ambientIndex sorts Γ 0)).2 ≤ bound
      rw [get_ambientIndex]
      exact bot_le)
  change Wf ((R, ⊥) :: fieldCtx sorts Γ) (.var (n + 1) : Expr Instruction)
    ((fieldCtx sorts Γ).get (ambientIndex sorts Γ 0)).1 bound at ambient
  rw [get_ambientIndex] at ambient
  have body : Wf ((R, ⊥) :: fieldCtx sorts Γ)
      (.op (Instruction.publish R) (.pair (.var 0) (.var (n + 1)))) X bound :=
    .op (f := Instruction.publish R) le_rfl (.pair (.var 0 bot_le) ambient)
  exact .step (.let1_beta literal body)

private abbrev sumOfProduct : Ty Unit := .coprod (.product X X) X
private abbrev productOfSum : Ty Unit := .product (.coprod X .unit) X

private abbrev productShape := (ReplyShape.inl (B := X) (.pair (.atom ()) (.atom ())))
private abbrev atomShape := (ReplyShape.inr (A := .product X X) (.atom ()))
private abbrev productLeft := (ReplyShape.pair (.inl (B := Ty.unit) (.atom ())) (.atom ()))
private abbrev productRight := (ReplyShape.pair (.inr (A := X) .unit) (.atom ()))

-- The two fields have the same sort and occupy distinct positions. The
-- ambient value comes after both fields. The other injection uses one slot.
example : productShape.specialize Γ (publish sumOfProduct) =
    .op (.publish sumOfProduct) (.pair (.inl (.pair (.var 0) (.var 1))) (.var 2)) := rfl
example : atomShape.specialize Γ (publish sumOfProduct) =
    .op (.publish sumOfProduct) (.pair (.inr (.var 0)) (.var 1)) := rfl

-- A product containing a sum exercises both the nested constructor order
-- and the unit branch, which contributes no new atom.
example : productLeft.specialize Γ (publish productOfSum) =
    .op (.publish productOfSum) (.pair (.pair (.inl (.var 0)) (.var 1)) (.var 2)) := rfl
example : productRight.specialize Γ (publish productOfSum) =
    .op (.publish productOfSum) (.pair (.pair (.inr .unit) (.var 0)) (.var 1)) := rfl

example : bound < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

example : Eqv Γ X bound (.let₁ (request sumOfProduct) (rebind sumOfProduct))
    (.let₁ (request sumOfProduct) (publish sumOfProduct)) :=
  acrossReply sumOfProduct

example : Eqv Γ X bound (.let₁ (request productOfSum) (rebind productOfSum))
    (.let₁ (request productOfSum) (publish productOfSum)) :=
  acrossReply productOfSum

private theorem flatAtoms {n : Nat} (i : Fin (List.replicate n (X, (⊥ : Eff))).length) :
    ∃ a, ((List.replicate n (X, (⊥ : Eff))).get i).1 = Ty.base a :=
  ⟨(), by simp [List.get_eq_getElem]⟩

private def sumCover : ConstructorCover (context sumOfProduct) :=
  .sum (0 : Fin 2) rfl rfl
    (.product (0 : Fin 2) rfl rfl (.atomic (flatAtoms (n := 3)))) (.atomic (flatAtoms (n := 2)))

private def productCover : ConstructorCover (context productOfSum) :=
  .product (0 : Fin 2) rfl rfl
    (.sum (1 : Fin 3) rfl rfl (.atomic (flatAtoms (n := 3)))
      (.unit (1 : Fin 3) rfl rfl (.atomic (flatAtoms (n := 2)))))

-- The existing renderer puts a pair let under the left arm of the case.
example : sumCover.render (fun _ a => a) (publish sumOfProduct) =
    .case (.var 0)
      (.let₂ (.var 0) (.op (.publish sumOfProduct) (.pair (.inl (.pair (.var 1) (.var 0))) (.var 4))))
      (.op (.publish sumOfProduct) (.pair (.inr (.var 0)) (.var 2))) := rfl

example : Eqv Γ X bound (.let₁ (request sumOfProduct) (publish sumOfProduct))
    (.let₁ (request sumOfProduct) (sumCover.render (fun _ a => a) (publish sumOfProduct))) :=
  .let1 (.refl (requestWf _)) (sumCover.eqv_rebuild (publishWf _))

example : Eqv Γ X bound (.let₁ (request productOfSum) (publish productOfSum))
    (.let₁ (request productOfSum) (productCover.render (fun _ a => a) (publish productOfSum))) :=
  .let1 (.refl (requestWf _)) (productCover.eqv_rebuild (publishWf _))

private abbrev nativePublish (R : Ty Unit) : Tm Empty Instruction 2 :=
  .op (.publish R) (.pair (.bv 0) (.bv 1))

example :
    HasTypeEffect (Ctx.nil : Ctx Empty (Ty Unit)) (fieldCtx _ Γ).toBoundCtx
      ((nativePublish sumOfProduct).bsubst (productShape.nativeSubst Γ)) X bound :=
  specialize_hasTypeEffect productShape (publishWf sumOfProduct) rfl

private abbrev nativeRebind (R : Ty Unit) : Tm Empty Instruction 2 :=
  .let₁ (.bv 0) (.op (.publish R) (.pair (.bv 0) (.bv 2)))

example :
    AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty (Ty Unit)) (fieldCtx _ Γ).toBoundCtx
      ((nativeRebind productOfSum).bsubst (productRight.nativeSubst Γ))
      ((nativePublish productOfSum).bsubst (productRight.nativeSubst Γ)) X := by
  have body : Wf ((productOfSum, ⊥) :: context productOfSum)
      (.op (Instruction.publish productOfSum) (.pair (.var 0) (.var 2))) X bound :=
    .op (f := Instruction.publish productOfSum) le_rfl (.pair (.var 0 bot_le) (.var 2 bot_le))
  have eq : Eqv (context productOfSum) X bound (rebind productOfSum) (publish productOfSum) :=
    .step (.let1_beta (.var 0 le_rfl) body)
  exact native_specialize productRight (a := rebind productOfSum) (b := publish productOfSum)
    pureCtx rfl rfl (eq.toLetIter rfl rfl)

-- The empty reply has no constructor specializations. The request still
-- occurs once on each side, and only its impossible continuation changes.
example : Eqv Γ X bound (.let₁ (request .empty) (.abort (.var 0))) (.let₁ (request .empty) (.var 1)) := by
  apply eqv_let_of_specializations atomicCtx pureCtx (requestWf .empty) (.abort (.var 0 bot_le)) (.var 1 bot_le)
  intro n sorts shape
  cases shape

-- The recursive continuation theorem applies to this whole-reply use,
-- which the earlier finite endpoint grammar does not recognize.
example : ¬ Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Written
    X bound Γ (.let₁ (request sumOfProduct) (publish sumOfProduct)) := by
  intro written
  cases written with
  | ret _ leaf => cases leaf
  | call _ ty _ _ _ _ => cases ty

end LetIterRecursiveReplyFixture

namespace LetIterSharedReplyReflectionFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured (ReplyShape)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape
  (fieldCtx fieldIndex)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile ConstructorLeaf)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection
  (Shared Written shape_constructor written_reflection independent_written_reflection call_request_inversion)

set_option backward.isDefEq.respectTransparency false

private abbrev T := Ty Unit
private abbrev X : T := .base ()
private abbrev R : T := .coprod (.product X X) (.product .unit X)
private abbrev Eff := Bool × Bool
private abbrev bound : Eff := (true, false)

private inductive Instruction
  | receive | send | discard | stop | sendTagged | stopAlt | tick

private instance : HasTy Instruction T where
  src
    | .send => R
    | .sendTagged => .product R .unit
    | _ => .unit
  trg
    | .receive => R
    | .stop | .stopAlt => .empty
    | _ => .unit

private instance : HasEff Instruction Eff where
  eff
    | .discard => ⊥
    | _ => bound

local instance : EffectIteration Eff := EffectIteration.complete Eff

private theorem receiveVisible : ¬ IsPure (⊥ : Eff) Instruction.receive :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private theorem sendVisible : ¬ IsPure (⊥ : Eff) Instruction.send :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private theorem stopVisible : ¬ IsPure (⊥ : Eff) Instruction.stop :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private def profile : Profile (α := Unit) Instruction Eff := fun f h => by
  cases f
  case discard => exact .unit rfl
  all_goals exact (show False from Bool.noConfusion (congrArg Prod.fst h)).elim

private abbrev Γ : EffectCtx T Eff := []
private theorem pureCtx : Γ.Pure := fun i => i.elim0
private abbrev slots : Fin Γ.length → Unit := Fin.elim0
private theorem slotTy : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots i) :=
  fun i => i.elim0

private abbrev tailLeft : Expr Instruction :=
  .let₁ (.op .send (.var 0)) (.op .discard (.var 0))
private abbrev tailRight : Expr Instruction :=
  .let₁ (.op .send (.var 0)) .unit

private abbrev left : Expr Instruction := .let₁ (.op .receive .unit) tailLeft
private abbrev right : Expr Instruction := .let₁ (.op .receive .unit) tailRight

private theorem leftWf : Wf ((R, ⊥) :: Γ) tailLeft .unit bound :=
  .let₁ (.op (f := Instruction.send) le_rfl (.var 0 bot_le))
    (.op (f := Instruction.discard) bot_le (.var 0 bot_le))

private theorem rightWf : Wf ((R, ⊥) :: Γ) tailRight .unit bound :=
  .let₁ (.op (f := Instruction.send) le_rfl (.var 0 bot_le)) (.unit _ _)

private theorem shared : Shared .unit bound Γ left right := by
  refine .call (f := Instruction.receive) receiveVisible le_rfl (.unit _ _) .unit leftWf rightWf ?_
  intro n sorts shape
  let Δ := fieldCtx sorts Γ
  let reply : Expr Instruction := shape.source (fieldIndex sorts Γ)
  change Shared .unit bound Δ
    (.let₁ (.op .send reply) (.op .discard (.var 0))) (.let₁ (.op .send reply) .unit)
  refine .call (f := Instruction.send) sendVisible le_rfl ?_ (shape_constructor shape (fieldIndex sorts Γ))
    (.op (f := Instruction.discard) bot_le (.var 0 bot_le)) (.unit _ _) ?_
  · exact shape.wf (fieldIndex sorts Γ)
      (Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.get_fieldIndex
        (Γ := Γ))
  · intro m ts unitReply
    cases unitReply
    exact .leaf (.op (f := Instruction.discard) le_rfl (.unit _ _)) (.unit _ _) (.op .unit) .unit

private abbrev nativeLeft : Tm Empty Instruction 0 :=
  .let₁ (.op .receive .unit) (.let₁ (.op .send (.bv 0)) (.op .discard (.bv 0)))
private abbrev nativeRight : Tm Empty Instruction 0 :=
  .let₁ (.op .receive .unit) (.let₁ (.op .send (.bv 0)) .unit)

example : bound < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

-- The second visible request consumes the whole nested reply. The
-- specialized unit leaves agree by the bottom-pure terminality equation.
example : AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx nativeLeft nativeRight .unit ↔
    Eqv Γ .unit bound left right :=
  written_reflection profile pureCtx slotTy shared rfl rfl

-- Construct the native equation using the native pure-let and unit laws,
-- then reflect it to the original written judgment.
example : Eqv Γ .unit bound left right := by
  have typed : HasType Instruction (Ctx.nil : Ctx Empty T)
      (.snoc (.snoc Γ.toBoundCtx R) .unit) (.op Instruction.discard (.bv 0)) (.unit : T) :=
    .op .bv
  have finish : Equiv (⊥ : Eff) (Ctx.nil : Ctx Empty T)
      (.snoc (.snoc Γ.toBoundCtx R) .unit) (.op Instruction.discard (.bv 0)) .unit (.unit : T) :=
    (Equiv.unitEta typed).symm.trans (Equiv.letBeta (.op rfl .bv) typed .unit)
  have native : AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx nativeLeft nativeRight .unit :=
    .equiv (.let₁ (.refl (.op .unit)) (.let₁ (.refl (.op .bv)) finish))
  exact (written_reflection profile pureCtx slotTy shared rfl rfl).mp native

example : ¬ Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Written
    .unit bound Γ left := by
  intro h
  cases h with
  | ret _ leaf => cases leaf
  | call _ ty _ _ _ _ => cases ty

private abbrev stopLeft : Expr Instruction := .let₁ (.op .stop .unit) (.abort (.var 0))
private abbrev stopRight : Expr Instruction := .let₁ (.op .stop .unit) .unit

private theorem stopShared : Shared .unit bound Γ stopLeft stopRight := by
  refine .call (f := Instruction.stop) stopVisible le_rfl (.unit _ _) .unit
    (.abort (.var 0 bot_le)) (.unit _ _) ?_
  intro n sorts shape
  cases shape

-- The visible empty-reply request is shared, and there is no branch to test.
example :
    AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx
      (.let₁ (.op Instruction.stop .unit) (.abort (.bv 0)))
      (.let₁ (.op Instruction.stop .unit) .unit) .unit ↔
    Eqv Γ .unit bound stopLeft stopRight :=
  written_reflection profile pureCtx slotTy stopShared rfl rfl

private abbrev branch : Expr Instruction :=
  .let₁ (.op .receive .unit) (.case (.var 0) .unit .unit)

private abbrev done : Expr Instruction :=
  .let₁ (.op .receive .unit) .unit

private theorem branchShared : Shared .unit bound Γ branch done := by
  refine .call (f := Instruction.receive) receiveVisible le_rfl (.unit _ _) .unit
    (.case (.var 0 bot_le) (.unit _ _) (.unit _ _)) (.unit _ _) ?_
  intro n sorts shape
  refine .normalize (a' := .unit) (b' := .unit) ?_ (.refl (.unit _ _))
    (.leaf (.unit _ _) (.unit _ _) .unit .unit)
  cases shape with
  | inl payload =>
    have typed := payload.wf (Φ := Instruction) (fieldIndex sorts Γ)
      (Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.get_fieldIndex
        (Γ := Γ))
    exact (KnownTag.case_eqv (B := Ty.product .unit X) (.inl (typed.weakenEffect bot_le)) (.unit _ _) (.unit _ _)).trans
      (.step (.let1_beta typed (.unit _ _)))
  | inr payload =>
    have typed := payload.wf (Φ := Instruction) (fieldIndex sorts Γ)
      (Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.get_fieldIndex
        (Γ := Γ))
    exact (KnownTag.case_eqv (A := Ty.product X X) (.inr (typed.weakenEffect bot_le)) (.unit _ _) (.unit _ _)).trans
      (.step (.let1_beta typed (.unit _ _)))

-- The optional normalization step uses the selected constructor's typed
-- case reduction certificate. It still compares at the same bound.
example :
    AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx
      (.let₁ (.op Instruction.receive .unit) (.case (.bv 0) .unit .unit))
      (.let₁ (.op Instruction.receive .unit) .unit) .unit ↔
    Eqv Γ .unit bound branch done :=
  written_reflection profile pureCtx slotTy branchShared rfl rfl

private theorem taggedVisible : ¬ IsPure (⊥ : Eff) Instruction.sendTagged :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private theorem stopAltVisible : ¬ IsPure (⊥ : Eff) Instruction.stopAlt :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private abbrev tag (raw : Bool) : Expr Instruction :=
  if raw then .op .discard .unit else .unit

private theorem tagWf (Δ : EffectCtx T Eff) (raw : Bool) :
    Wf Δ (tag raw) .unit (⊥ : Eff) := by
  cases raw
  · exact .unit _ _
  · exact .op (f := Instruction.discard) le_rfl (.unit _ _)

private theorem tagLeaf (raw : Bool) : ConstructorLeaf (tag raw) := by
  cases raw
  · exact .unit
  · exact .op .unit

private abbrev sendTail (raw : Bool) : Expr Instruction :=
  .let₁ (.op .sendTagged (.pair (.var 0) (tag raw))) .unit

private abbrev withTag (raw : Bool) : Expr Instruction :=
  .let₁ (.op .receive .unit) (sendTail raw)

private theorem withTagWritten (raw : Bool) : Written .unit bound Γ (withTag raw) := by
  have tail : Wf ((R, ⊥) :: Γ) (sendTail raw) .unit bound :=
    .let₁ (.op (f := Instruction.sendTagged) le_rfl
      (.pair (.var 0 bot_le) ((tagWf _ raw).weakenEffect bot_le))) (.unit _ _)
  refine Written.of_call (f := Instruction.receive) receiveVisible le_rfl (.unit _ _) .unit tail ?_
  intro n sorts shape
  let Δ := fieldCtx sorts Γ
  let reply : Expr Instruction := shape.source (fieldIndex sorts Γ)
  have expanded : shape.specialize Γ (sendTail raw) =
      .let₁ (.op .sendTagged (.pair reply (tag raw))) .unit := by
    cases raw <;> rfl
  rw [expanded]
  have arg : Wf Δ reply R (⊥ : Eff) := shape.wf (fieldIndex sorts Γ)
    (Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.get_fieldIndex
      (Γ := Γ))
  refine Written.of_call (f := Instruction.sendTagged) taggedVisible le_rfl
    (.pair arg (tagWf _ raw)) (.pair (shape_constructor shape (fieldIndex sorts Γ)) (tagLeaf raw))
    (.unit _ _) ?_
  intro m ts shape'
  exact Written.of_leaf (.unit _ _) .unit

private abbrev nativeWithTag (raw : Bool) : Tm Empty Instruction 0 :=
  .let₁ (.op .receive .unit)
    (.let₁ (.op .sendTagged (.pair (.bv 0) (if raw then .op .discard .unit else .unit))) .unit)

-- The raw arguments differ only after a whole nested reply is in scope.
-- Each witness is constructed from its own syntax.
example : Eqv Γ .unit bound (withTag true) (withTag false) := by
  have typed : HasType Instruction (Ctx.nil : Ctx Empty T) (Γ.toBoundCtx.snoc R)
      (.op Instruction.discard .unit) (.unit : T) := .op .unit
  have argEq : Equiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) (Γ.toBoundCtx.snoc R)
      (.op Instruction.discard .unit) .unit (.unit : T) :=
    (Equiv.unitEta typed).symm.trans (Equiv.letBeta (.op rfl .unit) typed .unit)
  have native : AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx
      (nativeWithTag true) (nativeWithTag false) .unit :=
    .equiv (.let₁ (.refl (.op .unit)) (.let₁ (.op (.pair (.refl .bv) argEq)) .unit))
  exact (independent_written_reflection profile pureCtx slotTy
    (withTagWritten true) (withTagWritten false) rfl rfl).mp native

-- Even with the same typed argument and no possible reply, different
-- visible opcodes cannot be identified.
example : ¬ AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx
    (.let₁ (.op Instruction.stop .unit) .unit)
    (.let₁ (.op Instruction.stopAlt .unit) .unit) (.unit : T) := by
  intro h
  have result := call_request_inversion profile pureCtx slotTy (e := bound)
    (f := Instruction.stop) (g := Instruction.stopAlt)
    (arg := .unit) (arg' := .unit) (k := .unit) (l := .unit)
    stopVisible stopAltVisible (.unit _ _) (.unit _ _) .unit .unit
    (.unit _ _) (.unit _ _) rfl rfl h
  cases result.1

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
  (Raw raw_reflection)

private theorem tickVisible : ¬ IsPure (⊥ : Eff) Instruction.tick :=
  fun h => Bool.noConfusion (congrArg Prod.fst h)

private abbrev nestedArgs : Expr Instruction :=
  .op .sendTagged (.pair (.op .receive .unit) (.op .tick .unit))

private abbrev splitArgs : Expr Instruction :=
  .let₁ (.op .receive .unit) (.op .sendTagged (.pair (.var 0) (.op .tick .unit)))

private abbrev orderedCalls : Expr Instruction :=
  .let₁ (.op .receive .unit)
    (.let₁ (.op .tick .unit) (.op .sendTagged (.pair (.var 1) (.var 0))))

private theorem receiveRaw (Δ : EffectCtx T Eff) :
    Raw bound Δ R (.op Instruction.receive .unit) :=
  .call receiveVisible le_rfl (.leaf (.unit _ _) .unit)

private theorem tickRaw (Δ : EffectCtx T Eff) :
    Raw bound Δ .unit (.op Instruction.tick .unit) :=
  .call tickVisible le_rfl (.leaf (.unit _ _) .unit)

private theorem nestedArgsRaw : Raw bound Γ .unit nestedArgs :=
  .call taggedVisible le_rfl (.pair (receiveRaw _) (tickRaw _))

private theorem splitArgsRaw : Raw bound Γ .unit splitArgs :=
  .let1 (receiveRaw _) (.call taggedVisible le_rfl
    (.pair (.leaf (.var 0 le_rfl) (.var 0)) (tickRaw _)))

private theorem nestedArgs_order : Eqv Γ .unit bound nestedArgs orderedCalls := by
  have receive : Wf Γ (.op Instruction.receive .unit) R bound := .op le_rfl (.unit _ _)
  have tick : Wf Γ (.op Instruction.tick .unit) .unit bound := .op le_rfl (.unit _ _)
  have tickUnder : Wf ((R, ⊥) :: Γ) (.op Instruction.tick .unit) .unit bound :=
    .op le_rfl (.unit _ _)
  have args : Wf ((.unit, ⊥) :: (R, ⊥) :: Γ) (.pair (.var 1) (.var 0) : Expr Instruction)
      (.product R .unit) bound := .pair (.var 1 bot_le) (.var 0 bot_le)
  exact (Eqv.op (f := Instruction.sendTagged) le_rfl (CallByValue.pair_bind receive tick)).trans
    ((CallByValue.op_let (f := Instruction.sendTagged) le_rfl receive (.let₁ tickUnder args)).trans
      (.let1 (.refl receive) (CallByValue.op_let (f := Instruction.sendTagged) le_rfl tickUnder args)))

private theorem splitArgs_order : Eqv Γ .unit bound splitArgs orderedCalls := by
  have receive : Wf Γ (.op Instruction.receive .unit) R bound := .op le_rfl (.unit _ _)
  have tick : Wf ((R, ⊥) :: Γ) (.op Instruction.tick .unit) .unit bound := .op le_rfl (.unit _ _)
  have value : Wf ((R, ⊥) :: Γ) (.var 0 : Expr Instruction) R (⊥ : Eff) := .var 0 le_rfl
  have body : Wf ((R, ⊥) :: (R, ⊥) :: Γ)
      (.let₁ (.op Instruction.tick .unit) (.pair (.var 1) (.var 0))) (.product R .unit) bound :=
    .let₁ (.op le_rfl (.unit _ _)) (.pair (.var 1 bot_le) (.var 0 bot_le))
  have pairOrder := (CallByValue.pair_bind (value.weakenEffect bot_le) tick).trans
    (.step (.let1_beta value body))
  exact .let1 (.refl receive) ((Eqv.op (f := Instruction.sendTagged) le_rfl pairOrder).trans
    (CallByValue.op_let (f := Instruction.sendTagged) le_rfl tick (.pair (.var 1 bot_le) (.var 0 bot_le))))

-- Both inputs are independently recognized before normalization. The
-- structured receive reply becomes the first field of the final request.
example : Eqv Γ .unit bound nestedArgs splitArgs := by
  have lowers : orderedCalls.toLetIter 0 = some
      (.let₁ (.op .receive .unit)
        (.let₁ (.op .tick .unit) (.op .sendTagged (.pair (.bv 1) (.bv 0))))) := rfl
  exact (raw_reflection profile pureCtx slotTy nestedArgsRaw splitArgsRaw rfl rfl).mp
    ((nestedArgs_order.toLetIter rfl lowers).trans (splitArgs_order.toLetIter rfl lowers).symm)

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
  (CaseRaw case_reflection let_case_eqv let2_pair_eqv)

private abbrev branchLeft : Expr Instruction :=
  .op .sendTagged (.pair (.inl (.var 0)) .unit)

private abbrev branchRight : Expr Instruction :=
  .op .send (.inr (.var 0))

private abbrev caseScrutinee : Expr Instruction :=
  .op .receive (.op .tick .unit)

private abbrev branchDirect : Expr Instruction :=
  .case caseScrutinee branchLeft branchRight

private abbrev branchBound : Expr Instruction :=
  .let₁ caseScrutinee (.case (.var 0) branchLeft branchRight)

private theorem leftRaw (Δ : EffectCtx T Eff) :
    CaseRaw bound ((.product X X, ⊥) :: Δ) .unit branchLeft :=
  .straight (.call taggedVisible le_rfl
    (.leaf (.pair (.inl (.var 0 le_rfl)) (.unit _ _)) (.pair (.inl (.var 0)) .unit)))

private theorem rightRaw (Δ : EffectCtx T Eff) :
    CaseRaw bound ((.product .unit X, ⊥) :: Δ) .unit branchRight :=
  .straight (.call sendVisible le_rfl (.leaf (.inr (.var 0 le_rfl)) (.inr (.var 0))))

private theorem caseScrutineeRaw : Raw bound Γ R caseScrutinee :=
  .call receiveVisible le_rfl (tickRaw Γ)

private theorem branchDirectRaw : CaseRaw bound Γ .unit branchDirect :=
  .case caseScrutineeRaw (leftRaw Γ) (rightRaw Γ)

private theorem branchBoundRaw : CaseRaw bound Γ .unit branchBound :=
  .let1 caseScrutineeRaw (.case (.leaf (.var 0 le_rfl) (.var 0)) (leftRaw _) (rightRaw _))

private abbrev nativeScrutinee : Tm Empty Instruction 0 :=
  .op .receive (.op .tick .unit)
private abbrev nativeBranchL {n : Nat} : Tm Empty Instruction (n + 1) :=
  .op .sendTagged (.pair (.inl (.bv 0)) .unit)
private abbrev nativeBranchR {n : Nat} : Tm Empty Instruction (n + 1) :=
  .op .send (.inr (.bv 0))
private abbrev nativeDirect : Tm Empty Instruction 0 :=
  .case nativeScrutinee nativeBranchL nativeBranchR
private abbrev nativeBound : Tm Empty Instruction 0 :=
  .let₁ nativeScrutinee (.case (.bv 0) nativeBranchL nativeBranchR)

-- The independent recognizers start from raw case and raw let/case syntax.
-- The scrutinee makes two requests before either arm can make its request.
example : Eqv Γ .unit bound branchDirect branchBound := by
  have native : AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx nativeDirect nativeBound .unit :=
    .equiv (.ax (.sequencing (.bindCase nativeScrutinee nativeBranchL nativeBranchR))
      (.case (.op (.op .unit)) (.op (.pair (.inl .bv) .unit)) (.op (.inr .bv)))
      (.let₁ (.op (.op .unit)) (.case .bv (.op (.pair (.inl .bv) .unit)) (.op (.inr .bv)))))
  exact (case_reflection profile pureCtx slotTy branchDirectRaw branchBoundRaw rfl rfl).mp native

private def leftReply : ReplyShape (fun _ : Fin 2 => ()) R :=
  .inl (.pair (.atom ()) (.atom ()))

private abbrev ΔLeft := fieldCtx (fun _ : Fin 2 => ()) Γ
private abbrev leftPayload : Expr Instruction := .pair (.var 0) (.var 1)
private abbrev selectedLeft : Expr Instruction :=
  .op .sendTagged (.pair (.inl leftPayload) .unit)

private theorem leftPayloadWf : Wf ΔLeft leftPayload (.product X X) (⊥ : Eff) :=
  .pair (Wf.var (Γ := ΔLeft) ⟨0, by decide⟩ le_rfl) (Wf.var (Γ := ΔLeft) ⟨1, by decide⟩ le_rfl)

private theorem specializeLeft {body arm : Expr Instruction}
    (hw : Wf ((.product .unit X, ⊥) :: ΔLeft) arm .unit bound)
    (eq : leftReply.specialize Γ body = (.case (.inl leftPayload) branchLeft arm)) :
    Eqv ΔLeft .unit bound (leftReply.specialize Γ body) selectedLeft := by
  rw [eq]
  have hl : Wf ((.product X X, ⊥) :: ΔLeft) branchLeft .unit bound :=
    .op le_rfl (.pair (.inl (.var 0 bot_le)) (.unit _ _))
  have hp := leftPayloadWf.weakenEffect (show (⊥ : Eff) ≤ bound from bot_le)
  exact (Eqv.step (.reduce (.case (.inl hp) hl hw) (.let₁ hp hl) (.case_inl _ _ _))).trans
    (.step (.let1_beta leftPayloadWf hl))

-- The reply supplies two distinct slots. The resulting continuation
-- performs sendTagged on that pair and bypasses the right-hand send.
example : Eqv ΔLeft .unit bound
    (leftReply.specialize Γ (.case (.var 0) branchLeft branchRight.wk1)) selectedLeft :=
  specializeLeft (.op le_rfl (.inr (.var 0 bot_le))) rfl

-- Changing the untaken right arm to a tick preserves the left specialization.
example : Eqv ΔLeft .unit bound
    (leftReply.specialize Γ (.case (.var 0) branchLeft branchRight.wk1))
    (leftReply.specialize Γ (.case (.var 0) branchLeft (.op .tick .unit))) :=
  (specializeLeft (.op le_rfl (.inr (.var 0 bot_le))) rfl).trans
    (specializeLeft (.op (f := Instruction.tick) le_rfl (.unit _ _)) rfl).symm

private def rightReply : ReplyShape (fun _ : Fin 1 => ()) R :=
  .inr (.pair .unit (.atom ()))

private abbrev ΔRight := fieldCtx (fun _ : Fin 1 => ()) Γ
private abbrev rightPayload : Expr Instruction := .pair .unit (.var 0)

-- The other tag instead selects send with its own payload.
private theorem specializeRight : Eqv ΔRight .unit bound
    (rightReply.specialize Γ (.case (.var 0) branchLeft branchRight))
    (.op .send (.inr rightPayload)) := by
  have hp : Wf ΔRight rightPayload (.product .unit X) (⊥ : Eff) :=
    .pair (.unit _ _) (Wf.var (Γ := ΔRight) ⟨0, by decide⟩ le_rfl)
  have hl : Wf ((.product X X, ⊥) :: ΔRight) branchLeft .unit bound :=
    .op le_rfl (.pair (.inl (.var 0 bot_le)) (.unit _ _))
  have hr : Wf ((.product .unit X, ⊥) :: ΔRight) branchRight .unit bound :=
    .op le_rfl (.inr (.var 0 bot_le))
  have hw := hp.weakenEffect (show (⊥ : Eff) ≤ bound from bot_le)
  exact (Eqv.step (.reduce (.case (.inr hw) hl hr) (.let₁ hw hr) (.case_inr _ _ _))).trans
    (.step (.let1_beta hp hr))

private abbrev RequestArg : T := .product R .unit
private abbrev returnLeft : Expr Instruction := .pair (.inl (.var 0)) .unit
private abbrev returnRight : Expr Instruction := .pair (.inr (.var 0)) .unit
private abbrev postRequest : Expr Instruction := .op .sendTagged (.var 0)
private abbrev caseValue : Expr Instruction := .case caseScrutinee returnLeft returnRight
private abbrev consumeBound : Expr Instruction := .let₁ caseValue postRequest
private abbrev consumeDirect : Expr Instruction := .op .sendTagged caseValue
private abbrev consumeArms : Expr Instruction :=
  .case caseScrutinee (.let₁ returnLeft postRequest) (.let₁ returnRight postRequest)

private theorem returnLeftWf (Δ : EffectCtx T Eff) :
    Wf ((.product X X, ⊥) :: Δ) returnLeft RequestArg (⊥ : Eff) :=
  .pair (.inl (.var 0 le_rfl)) (.unit _ _)

private theorem returnRightWf (Δ : EffectCtx T Eff) :
    Wf ((.product .unit X, ⊥) :: Δ) returnRight RequestArg (⊥ : Eff) :=
  .pair (.inr (.var 0 le_rfl)) (.unit _ _)

private theorem postRequestWf (Δ : EffectCtx T Eff) :
    Wf ((RequestArg, ⊥) :: Δ) postRequest .unit bound :=
  .op le_rfl (.var 0 bot_le)

private theorem postRequestRaw (Δ : EffectCtx T Eff) :
    CaseRaw bound ((RequestArg, ⊥) :: Δ) .unit postRequest :=
  .straight (.call taggedVisible le_rfl (.leaf (.var 0 le_rfl) (.var 0)))

private theorem returnLeftRaw (Δ : EffectCtx T Eff) :
    CaseRaw bound ((.product X X, ⊥) :: Δ) RequestArg returnLeft :=
  .straight (.leaf (returnLeftWf Δ) (.pair (.inl (.var 0)) .unit))

private theorem returnRightRaw (Δ : EffectCtx T Eff) :
    CaseRaw bound ((.product .unit X, ⊥) :: Δ) RequestArg returnRight :=
  .straight (.leaf (returnRightWf Δ) (.pair (.inr (.var 0)) .unit))

private theorem caseValueRaw : CaseRaw bound Γ RequestArg caseValue :=
  .case caseScrutineeRaw (returnLeftRaw Γ) (returnRightRaw Γ)

private theorem consumeBoundRaw : CaseRaw bound Γ .unit consumeBound :=
  .bind caseValueRaw (postRequestRaw Γ)

private theorem consumeDirectRaw : CaseRaw bound Γ .unit consumeDirect :=
  .call taggedVisible le_rfl caseValueRaw

private theorem consumeArmsRaw : CaseRaw bound Γ .unit consumeArms :=
  .case caseScrutineeRaw (.bind (returnLeftRaw Γ) (postRequestRaw _))
    (.bind (returnRightRaw Γ) (postRequestRaw _))

private abbrev nativeReturnLeft : Tm Empty Instruction 1 := .pair (.inl (.bv 0)) .unit
private abbrev nativeReturnRight : Tm Empty Instruction 1 := .pair (.inr (.bv 0)) .unit
private abbrev nativeValue : Tm Empty Instruction 0 := .case nativeScrutinee nativeReturnLeft nativeReturnRight
private abbrev nativeConsumeBound : Tm Empty Instruction 0 := .let₁ nativeValue (.op .sendTagged (.bv 0))
private abbrev nativeConsumeArms : Tm Empty Instruction 0 :=
  .case nativeScrutinee (.let₁ nativeReturnLeft (.op .sendTagged (.bv 0)))
    (.let₁ nativeReturnRight (.op .sendTagged (.bv 0)))

private theorem nativeConsume : AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx
    nativeConsumeBound nativeConsumeArms .unit := by
  have left : HasType Instruction .nil (Γ.toBoundCtx.snoc (.product X X)) nativeReturnLeft RequestArg :=
    .pair (.inl .bv) .unit
  have right : HasType Instruction .nil (Γ.toBoundCtx.snoc (.product .unit X)) nativeReturnRight RequestArg :=
    .pair (.inr .bv) .unit
  exact .equiv (.ax (.sequencing (.bindLetCase nativeScrutinee nativeReturnLeft nativeReturnRight
    (.op .sendTagged (.bv 0)))) (.let₁ (.case (.op (.op .unit)) left right) (.op .bv))
    (.case (.op (.op .unit)) (.let₁ left (.op .bv)) (.let₁ right (.op .bv))))

-- The two raw endpoints are recognized independently at (true, false).
example : Eqv Γ .unit bound consumeBound consumeArms :=
  (case_reflection profile pureCtx slotTy consumeBoundRaw consumeArmsRaw rfl rfl).mp nativeConsume

-- The same case can also be written directly in the request's argument.
example : Eqv Γ .unit bound consumeDirect consumeArms := by
  have typed : Wf Γ caseValue RequestArg bound :=
    .case (.op le_rfl (.op le_rfl (.unit _ _)))
      ((returnLeftWf Γ).weakenEffect bot_le) ((returnRightWf Γ).weakenEffect bot_le)
  have seq := CallByValue.op_bind (f := Instruction.sendTagged) le_rfl typed
  have lowered : consumeDirect.toLetIter 0 = some (.op .sendTagged nativeValue) := rfl
  exact (case_reflection profile pureCtx slotTy consumeDirectRaw consumeArmsRaw rfl rfl).mp
    ((seq.toLetIter lowered (rfl : consumeBound.toLetIter 0 = some nativeConsumeBound)).trans nativeConsume)

private abbrev boundReply : Expr Instruction :=
  .let₁ (.case (.var 0) returnLeft returnRight) postRequest

private abbrev consumeReply : Expr Instruction :=
  .case (.var 0) (.let₁ returnLeft postRequest) (.let₁ returnRight postRequest)

private theorem specializeConsume {n : Nat} {sorts : Fin n → Unit} (shape : ReplyShape sorts R) :
    Eqv (fieldCtx sorts Γ) .unit bound (shape.specialize Γ boundReply) (shape.specialize Γ consumeReply) := by
  let Δ : EffectCtx T Eff := (R, ⊥) :: Γ
  have eq : Eqv Δ .unit bound boundReply consumeReply :=
    let_case_eqv (.var 0 bot_le) ((returnLeftWf Δ).weakenEffect bot_le)
      ((returnRightWf Δ).weakenEffect bot_le) (postRequestWf Δ)
  exact eq.subst_typed (fun i => shape.specialize_wf (Wf.var (Γ := Δ) i le_rfl))

private theorem returnLeftPost (Δ : EffectCtx T Eff) :
    Eqv ((.product X X, ⊥) :: Δ) .unit bound (.let₁ returnLeft postRequest) branchLeft :=
  .step (.let1_beta (returnLeftWf Δ) (postRequestWf _))

private abbrev requestRight : Expr Instruction := .op .sendTagged (.pair (.inr (.var 0)) .unit)

private theorem returnRightPost (Δ : EffectCtx T Eff) :
    Eqv ((.product .unit X, ⊥) :: Δ) .unit bound (.let₁ returnRight postRequest) requestRight :=
  .step (.let1_beta (returnRightWf Δ) (postRequestWf _))

-- Each explicit reply specialization leaves exactly one sendTagged, with
-- the result from its chosen arm. The request arguments retain distinct tags.
example : Eqv ΔLeft .unit bound (leftReply.specialize Γ boundReply) selectedLeft := by
  have tag : Wf ΔLeft (.inl leftPayload) R bound := .inl (leftPayloadWf.weakenEffect bot_le)
  exact (specializeConsume leftReply).trans
    ((Eqv.case (.refl tag) (returnLeftPost ΔLeft) (returnRightPost ΔLeft)).trans
      (specializeLeft (returnRightPost ΔLeft).endpoints_wf.2
        (rfl : leftReply.specialize Γ (.case (.var 0) branchLeft requestRight) = _)))

example : Eqv ΔRight .unit bound (rightReply.specialize Γ boundReply)
    (.op .sendTagged (.pair (.inr rightPayload) .unit)) := by
  have hp : Wf ΔRight rightPayload (.product .unit X) (⊥ : Eff) :=
    .pair (.unit _ _) (Wf.var (Γ := ΔRight) ⟨0, by decide⟩ le_rfl)
  have hw := hp.weakenEffect (show (⊥ : Eff) ≤ bound from bot_le)
  have left := (returnLeftPost ΔRight).endpoints_wf.2
  have right := (returnRightPost ΔRight).endpoints_wf.2
  exact (specializeConsume rightReply).trans
    ((Eqv.case (.refl (.inr hw)) (returnLeftPost ΔRight) (returnRightPost ΔRight)).trans
      ((Eqv.step (.reduce (.case (.inr hw) left right) (.let₁ hw right) (.case_inr _ _ _))).trans
        (.step (.let1_beta hp right))))

private abbrev rightChoice : Expr Instruction :=
  .case (.inl .unit) (.op .receive .unit) (.op .receive (.op .tick .unit))

private theorem rightChoiceRaw (Δ : EffectCtx T Eff) : CaseRaw bound Δ R rightChoice :=
  .branch (A := .unit) (B := .unit) (.straight (.leaf (.inl (.unit _ _)) (.inl .unit)))
    (.straight (receiveRaw _)) (.straight (.call receiveVisible le_rfl (tickRaw _)))

private theorem rightChoiceEqv (Δ : EffectCtx T Eff) :
    Eqv Δ R bound rightChoice (.op .receive .unit) := by
  have scrutinee : Wf Δ (.inl .unit : Expr Instruction) (.coprod .unit .unit) bound := .inl (.unit _ _)
  have left : Wf ((.unit, ⊥) :: Δ) (.op Instruction.receive .unit) R bound := .op le_rfl (.unit _ _)
  have right : Wf ((.unit, ⊥) :: Δ) (.op Instruction.receive (.op .tick .unit)) R bound :=
    .op le_rfl (.op le_rfl (.unit _ _))
  exact (Eqv.step (.reduce (.case scrutinee left right) (.let₁ (.unit _ _) left)
    (.case_inl _ _ _))).trans (.step (.let1_beta (.unit _ _) left))

-- Newest is the right result. Both fields occur exactly once in the request.
private abbrev useBoth : Expr Instruction :=
  .op .sendTagged (.pair (.var 0) (.var 1))

private theorem useBothWf (Δ : EffectCtx T Eff) :
    Wf ((R, ⊥) :: (.unit, ⊥) :: Δ) useBoth .unit bound :=
  .op le_rfl (.pair (.var 0 bot_le) (.var 1 bot_le))

private theorem useBothRaw (Δ : EffectCtx T Eff) :
    CaseRaw bound ((R, ⊥) :: (.unit, ⊥) :: Δ) .unit useBoth :=
  .straight (.call taggedVisible le_rfl
    (.leaf (.pair (.var 0 le_rfl) (.var 1 le_rfl)) (.pair (.var 0) (.var 1))))

private abbrev destructPair : Expr Instruction :=
  .let₂ (.pair branchDirect rightChoice) useBoth
private abbrev pairAsLets : Expr Instruction :=
  .let₁ branchDirect (.let₁ rightChoice useBoth)

private theorem destructPairRaw : CaseRaw bound Γ .unit destructPair :=
  .let2 (.pair branchDirectRaw (rightChoiceRaw Γ)) (useBothRaw Γ)

private theorem pairAsLetsRaw : CaseRaw bound Γ .unit pairAsLets :=
  .bind branchDirectRaw (.bind (rightChoiceRaw _) (useBothRaw Γ))

private abbrev nativeRightChoice {n : Nat} : Tm Empty Instruction n :=
  .case (.inl .unit) (.op .receive .unit) (.op .receive (.op .tick .unit))

private theorem nativeRightChoiceWf {n : Nat} (β : BoundCtx T n) :
    HasType Instruction .nil β nativeRightChoice R :=
  .case (B := .unit) (.inl .unit) (.op .unit) (.op (.op .unit))

private abbrev nativeUseBoth : Tm Empty Instruction 2 :=
  .op .sendTagged (.pair (.bv 0) (.bv 1))

-- Both operands branch. The native pair rule supplies the premise between
-- the independently recognized endpoints at the original strict bound.
example : Eqv Γ .unit bound destructPair pairAsLets := by
  have left : HasType Instruction .nil Γ.toBoundCtx nativeDirect .unit :=
    .case (.op (.op .unit)) (.op (.pair (.inl .bv) .unit)) (.op (.inr .bv))
  have consume : HasType Instruction .nil ((Γ.toBoundCtx.snoc .unit).snoc R) nativeUseBoth .unit :=
    .op (.pair .bv .bv)
  have native : AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty T) Γ.toBoundCtx
      (.let₂ (.pair nativeDirect nativeRightChoice) nativeUseBoth)
      (.let₁ nativeDirect (.let₁ nativeRightChoice nativeUseBoth)) .unit :=
    .equiv (.ax (.structural (.pairBeta nativeDirect nativeRightChoice nativeUseBoth))
      (.let₂ (.pair left (nativeRightChoiceWf _)) consume)
      (.let₁ left (.let₁ (nativeRightChoiceWf _) consume)))
  exact (case_reflection profile pureCtx slotTy destructPairRaw pairAsLetsRaw rfl rfl).mp native

private abbrev productReply : Expr Instruction :=
  .let₂ (.pair (.case (.var 0) branchLeft branchRight) rightChoice) useBoth

private theorem pairReplyOrder {Δ : EffectCtx T Eff} {a b : Expr Instruction}
    (chosen : Eqv Δ .unit bound a b) :
    Eqv Δ .unit bound (.let₂ (.pair a rightChoice) useBoth)
      (.let₁ b (.let₁ (.op .receive .unit) useBoth)) :=
  (let2_pair_eqv chosen.endpoints_wf.1 (rightChoiceEqv Δ).endpoints_wf.1 (useBothWf Δ)).trans
    (.let1 chosen (.let1 (rightChoiceEqv _) (.refl (useBothWf Δ))))

-- Either reply executes the left branch request, then the right operand's
-- receive, then one request that consumes the two results.
example : Eqv ΔLeft .unit bound (leftReply.specialize Γ productReply)
    (.let₁ selectedLeft (.let₁ (.op .receive .unit) useBoth)) :=
  pairReplyOrder (specializeLeft (body := .case (.var 0) branchLeft branchRight)
    (.op le_rfl (.inr (.var 0 bot_le))) rfl)

example : Eqv ΔRight .unit bound (rightReply.specialize Γ productReply)
    (.let₁ (.op .send (.inr rightPayload)) (.let₁ (.op .receive .unit) useBoth)) :=
  pairReplyOrder specializeRight

end LetIterSharedReplyReflectionFixture

namespace LetIterCaseRawWeakeningFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
  (CaseRaw instructionBound instructionBound_le packed_weaken_eq_iff_at packed_weaken_eq_iff_join)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection
  (call_request_inversion)

set_option backward.isDefEq.respectTransparency false

private abbrev T := Ty Unit
private abbrev Eff := Bool × Bool × Bool × Bool
private abbrev kept : Eff := (true, false, false, false)

private inductive Instr
  | read | write | unusedLeft | unusedRight

private instance : HasTy Instr T := ⟨fun _ => .unit, fun _ => .unit⟩
private instance : HasEff Instr Eff where
  eff
    | .read | .write => kept
    | .unusedLeft => (false, true, false, false)
    | .unusedRight => (false, false, true, false)

local instance : EffectIteration Eff := EffectIteration.complete Eff

private theorem visible (i : Instr) : ¬ IsPure (⊥ : Eff) i := by
  change (instrEff i : Eff) ≠ ⊥
  cases i <;> decide

private def profile : Profile (α := Unit) Instr Eff := fun i h => (visible i h).elim

private abbrev Γ : EffectCtx T Eff := []
private theorem pureCtx : Γ.Pure := fun i => i.elim0
private abbrev slots : Fin Γ.length → Unit := Fin.elim0
private theorem slotTy : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots i) := fun i => i.elim0

private abbrev selected : Expr Instr := .let₁ (.op .read .unit) (.op .write .unit)

private abbrev withUnused (i : Instr) : Expr Instr :=
  .case (.inl .unit) selected (.op i .unit)

private theorem selectedWf (Δ : EffectCtx T Eff) {e : Eff} (h : kept ≤ e) :
    Wf Δ selected .unit e :=
  .let₁ (.op h (.unit _ _)) (.op h (.unit _ _))

private theorem withUnusedEqv (i : Instr) {e : Eff} (h : kept ≤ e) (h' : instrEff i ≤ e) :
    Eqv Γ .unit e (withUnused i) selected := by
  have tag : Wf Γ (.inl .unit : Expr Instr) (.coprod .unit .unit) e := .inl (.unit _ _)
  have left := selectedWf ((.unit, ⊥) :: Γ) h
  have right : Wf ((.unit, ⊥) :: Γ) (.op i .unit) .unit e := .op h' (.unit _ _)
  exact (Eqv.step (.reduce (.case tag left right) (.let₁ (.unit _ _) left) (.case_inl _ _ _))).trans
    (.step (.let1_beta (.unit _ _) left))

private theorem emitRaw (Δ : EffectCtx T Eff) {e : Eff} (i : Instr) (h : instrEff i ≤ e) :
    CaseRaw e Δ .unit (.op i .unit) :=
  .call (visible i) h (.straight (.leaf (.unit _ _) .unit))

private theorem topCode (i : Instr) : CaseRaw (⊤ : Eff) Γ .unit (withUnused i) :=
  .branch (A := .unit) (B := .unit) (.straight (.leaf (.inl (.unit _ _)) (.inl .unit)))
    (.bind (emitRaw _ .read le_top) (emitRaw _ .write le_top)) (emitRaw _ i le_top)

private abbrev eLeft : Eff := instructionBound (withUnused Instr.unusedLeft)
private abbrev eRight : Eff := instructionBound (withUnused Instr.unusedRight)
private abbrev eBoth : Eff := eLeft ⊔ eRight

private theorem leftRaw : CaseRaw eLeft Γ .unit (withUnused .unusedLeft) :=
  (topCode .unusedLeft).at_bound_iff.mpr le_rfl

private theorem rightRaw : CaseRaw eRight Γ .unit (withUnused .unusedRight) :=
  (topCode .unusedRight).at_bound_iff.mpr le_rfl

private abbrev leftTerm : TypedExpr Instr Γ .unit eLeft := ⟨_, leftRaw.wf⟩
private abbrev rightTerm : TypedExpr Instr Γ .unit eRight := ⟨_, rightRaw.wf⟩
private abbrev common : Hom Instr (packType Γ) .unit (⊤ : Eff) :=
  weakenEffect le_top (denote rightTerm)

-- The independently inferred bounds are incomparable. Their join is still below top.
example : eLeft < eBoth ∧ eRight < eBoth ∧ eBoth < (⊤ : Eff) :=
  ⟨lt_of_le_of_ne le_sup_left (fun h => Bool.noConfusion (congrArg (fun x => x.2.2.1) h)),
   lt_of_le_of_ne le_sup_right (fun h => Bool.noConfusion (congrArg (fun x => x.2.1) h)),
   lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg (fun x => x.2.2.2) h))⟩

private theorem bothEqv : Eqv Γ .unit eBoth leftTerm.val rightTerm.val :=
  (withUnusedEqv .unusedLeft (by decide) (by decide)).trans
    (withUnusedEqv .unusedRight (by decide) (by decide)).symm

private theorem commonEq : weakenEffect le_top (denote leftTerm) = common :=
  (packed_weaken_eq_iff_join profile pureCtx slotTy leftTerm rightTerm leftRaw rightRaw le_top le_top).mpr bothEqv

-- An endpoint presented directly at the larger bound still reflects at the lower join.
example : Eqv Γ .unit eBoth leftTerm.val rightTerm.val := by
  let leftHi : TypedExpr Instr Γ .unit (⊤ : Eff) := ⟨leftTerm.val, wf_weakenEffect leftTerm.prop le_top⟩
  exact (packed_weaken_eq_iff_at profile pureCtx slotTy leftHi rightTerm
    (leftRaw.weakenEffect le_sup_left) (rightRaw.weakenEffect le_sup_right) le_rfl le_top le_top).mp commonEq

-- The right program's untaken instruction still contributes to source typing.
-- Equality in the common hom cannot reflect to the left bound alone.
example : ¬ Eqv Γ .unit eLeft leftTerm.val rightTerm.val := by
  intro eq
  exact (by decide : ¬ eRight ≤ eLeft) (instructionBound_le eq.endpoints_wf.2)

example : ¬ Eqv Γ .unit eRight leftTerm.val rightTerm.val := by
  intro eq
  exact (by decide : ¬ eLeft ≤ eRight) (instructionBound_le eq.endpoints_wf.1)

private abbrev reversed : Expr Instr := .let₁ (.op .write .unit) (.op .read .unit)
private theorem reversedRaw : CaseRaw kept Γ .unit reversed :=
  .bind (emitRaw _ .write le_rfl) (emitRaw _ .read le_rfl)
private abbrev reverseTerm : TypedExpr Instr Γ .unit kept := ⟨_, reversedRaw.wf⟩

-- Widening still distinguishes two visible requests executed in the wrong order.
example : weakenEffect le_top (denote reverseTerm) ≠ common := by
  intro eq
  have low := (packed_weaken_eq_iff_join profile pureCtx slotTy reverseTerm rightTerm
    reversedRaw rightRaw le_top le_top).mp eq
  have order := low.trans (withUnusedEqv .unusedRight (by decide) (by decide))
  have native := order.toLetIter
    (rfl : reversed.toLetIter 0 = some (.let₁ (.op .write .unit) (.op .read .unit)))
    (rfl : selected.toLetIter 0 = some (.let₁ (.op .read .unit) (.op .write .unit)))
  obtain ⟨head, _⟩ := call_request_inversion profile pureCtx slotTy (e := kept ⊔ eRight)
    (f := Instr.write) (g := Instr.read) (arg := .unit) (arg' := .unit)
    (k := .op .read .unit) (l := .op .write .unit)
    (visible _) (visible _) (.unit _ _) (.unit _ _) .unit .unit
    (.op (by decide) (.unit _ _)) (.op (by decide) (.unit _ _)) rfl rfl native
  cases head

end LetIterCaseRawWeakeningFixture

namespace LetIterRequestFeedbackFixture

open Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic (repairedDenoteInSyntax repairedDenoteInSyntax_eq_iff)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev T := Ty Unit
private abbrev A : T := .base ()
private abbrev Eff := Bool × Bool
private abbrev strict : Eff := (true, false)

private instance : HasTy Unit T := ⟨fun _ => A, fun _ => .coprod A A⟩
local instance : HasEff Unit Eff := ⟨fun _ => strict⟩
local instance : EffectIteration Eff := EffectIteration.complete Eff

private abbrev β : BoundCtx T 1 := .snoc .nil A
private abbrev Γ₀ := (Ctx.nil : Ctx Empty T)
private abbrev start : Tm Empty Unit 1 := .bv 0

private theorem typedNormalization :
    HasTypeEffect Γ₀ β (padded () start) A strict ∧
    HasTypeEffect Γ₀ β (loop () start) A strict ∧
      Equiv (⊥ : Eff) Γ₀ β (padded () start) (loop () start) A :=
  remove_unit_at_bound rfl .bv (.iter rfl bot_le (sup_le le_rfl bot_le))

example : strict < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

private def thinDerivation : Derivation Unit Γ₀ β (loop () start) A :=
  .iter .bv (.op .bv)

private def paddedDerivation : Derivation Unit Γ₀ β (padded () start) A :=
  .iter (.let₁ .bv (.pair .bv .unit)) (.case (.op (.let₂ .bv .bv)) (.inl .bv) (.inr (.pair .bv .unit)))

example : repairedDenoteInSyntax (⊥ : Eff) paddedDerivation =
    repairedDenoteInSyntax (⊥ : Eff) thinDerivation :=
  (repairedDenoteInSyntax_eq_iff (⊥ : Eff) paddedDerivation thinDerivation).mpr (.equiv typedNormalization.2.2)

private abbrev V (_ : Unit) : Type := Bool
private abbrev D := Ty.denote (Lifted V)
private abbrev E := Event (Φ := Unit) V

private theorem visible : ¬ IsPure (⊥ : Eff) () := by
  change strict ≠ (⊥ : Eff)
  decide

private def noPure : PureMaps (Φ := Unit) (ε := Eff) V :=
  fun i h => by
    cases i
    exact (visible h).elim

private def env (state : D A) : BoundEnv D β :=
  BoundEnv.snoc (fun i => Fin.elim0 i) state

private def step (state : D A) : ITree.Tree E (D A ⊕ D A) :=
  ITree.vis (.call () state.down) (fun reply => ITree.ret ((toSmall V (.coprod A A)).symm reply))

private noncomputable def run (state : D A) : ITree.Tree E (D A) :=
  Silmaril.Elgot.iter step state

private theorem denote_thin (state : D A) :
    thinDerivation.denote D (instructions V noPure) (fun x => x.elim) (env state) = run state := by
  unfold thinDerivation
  erw [Derivation.denote]
  simp only [Derivation.denote, pure_bind, env, BoundEnv.snoc_zero, run]
  congr 1
  funext input
  change ((instructions V noPure).eval () input >>= fun reply => pure reply) = step input
  rw [eval_bind_of_not_pure V noPure visible]
  rfl

private theorem run_unfold (state : D A) :
    run state = ITree.vis (.call () state.down)
      (Sum.elim (fun output => ITree.ret ⟨output⟩) (fun next => run ⟨next⟩)) := by
  unfold run
  nth_rw 1 [congrFun (ITree.iterate_fixpoint step) state]
  change (ITree.vis _ _ >>= _) = _
  rw [ITree.vis_bind]
  congr 1
  funext reply
  cases reply <;> erw [pure_bind] <;> rfl

-- Repaired soundness transfers the same response-indexed observation to the padded loop.
example (state : D A) :
    paddedDerivation.denote D (instructions V noPure) (fun x => x.elim) (env state) =
      ITree.vis (.call () state.down)
        (Sum.elim (fun output => ITree.ret ⟨output⟩) (fun next => run ⟨next⟩)) := by
  rw [sound V noPure (.equiv typedNormalization.2.2) paddedDerivation thinDerivation (env state),
    denote_thin, run_unfold]

-- Choosing different repeat replies changes the very next request argument.
example : headRequest V (run ⟨false⟩) ≠ headRequest V (run ⟨true⟩) := by
  rw [run_unfold ⟨false⟩, run_unfold ⟨true⟩, head_of_vis, head_of_vis]
  intro h
  have heads := Part.some_injective h
  cases heads

example (state : D A) (d : Nat) :
    ¬ ITree.VisibleDepthLE
      (thinDerivation.denote D (instructions V noPure) (fun x => x.elim) (env state)) d := by
  rw [denote_thin]
  intro depth
  have longer := ITree.hasVisiblePrefix_iter step
    (fun s => ⟨Bool ⊕ Bool, .call () s.down, _, .inr (!s.down), ⟨!s.down⟩, rfl, rfl⟩)
    (d + 1) state
  exact Nat.not_succ_le_self d (depth _ longer)

end LetIterRequestFeedbackFixture

namespace LetIterObservedFeedbackFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
  (repairedDenoteInSyntax repairedDenoteInSyntax_eq_iff)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev U : Ty Unit := .unit
private abbrev Bit : Ty Unit := .coprod U U
private abbrev Eff := Bool × Bool
private abbrev strict : Eff := (true, false)

local instance : HasTy Unit (Ty Unit) := ⟨fun _ => Bit, fun _ => Bit⟩
local instance : HasEff Unit Eff := ⟨fun _ => strict⟩
local instance : EffectIteration Eff := EffectIteration.complete Eff

private abbrev V (_ : Unit) : Type := Unit
private abbrev D := Ty.denote (Lifted V)

private def code (right : Bool) : D Bit :=
  if right then .inr PUnit.unit else .inl PUnit.unit
private def embed (_ : D U) : D Bit := code false

private def leftTable : Machine V () (D U) (D U) :=
  ⟨fun s => toSmall V Bit (embed s), fun _ r => (toSmall V Bit).symm r⟩

private def rightTable (right : Bool) : Machine V () (D Bit) (D U) :=
  ⟨toSmall V Bit, fun _ r => match (toSmall V Bit).symm r with
    | .inl v => .inl v
    | .inr _ => .inr (code right)⟩

private theorem right_commutes : Commutes leftTable (rightTable false) embed := by
  intro s
  refine ⟨rfl, fun r => ?_⟩
  cases r <;> rfl

private theorem repeat_code_of_observation {b : Bool}
    (obs : leftTable.run PUnit.unit = (rightTable b).run (code false)) : b = false := by
  have reaches (s : D U) : leftTable.Reaches PUnit.unit s := by
    cases s
    exact .initial
  obtain ⟨_, commute, initial⟩ :=
    exists_commutes_of_initial (toSmall V Bit).injective reaches obs
  have step := (commute PUnit.unit).2 (.inr PUnit.unit)
  have next : code false = code b := initial.symm.trans (Sum.inr.inj step)
  cases b with
  | false => rfl
  | true => cases next

private abbrev Γ₀ := (Ctx.nil : Ctx Empty (Ty Unit))
private abbrev Γ : EffectCtx (Ty Unit) Eff := []
private abbrev Δ : EffectCtx (Ty Unit) Eff := [(U, ⊥)]

private abbrev bit (b : Bool) : Expr Unit := if b then .inr .unit else .inl .unit
private abbrev nativeBit {n : Nat} (b : Bool) : Tm Empty Unit n :=
  if b then .inr .unit else .inl .unit
private abbrev nativeEmbed : Tm Empty Unit 1 := .inl .unit
private abbrev bodyL : Tm Empty Unit 1 := .op () (.inl .unit)
private abbrev bodyR (b : Bool) : Tm Empty Unit 1 :=
  .case (.op () (.let₁ (.bv 0) (.bv 0))) (.inl (.bv 0)) (.inr (nativeBit b))

private abbrev loopL : Tm Empty Unit 0 := .iter .unit bodyL
private abbrev loopR (b : Bool) : Tm Empty Unit 0 :=
  .iter (.let₁ .unit nativeEmbed) (bodyR b)

private def bitDeriv {n : Nat} {β : BoundCtx (Ty Unit) n} (b : Bool) :
    Derivation Unit Γ₀ β (nativeBit b) Bit := by
  cases b
  · exact .inl .unit
  · exact .inr .unit

private def leftDeriv : Derivation Unit Γ₀ .nil loopL U :=
  .iter .unit (.op (.inl .unit))

private def rightDeriv (b : Bool) : Derivation Unit Γ₀ .nil (loopR b) U :=
  .iter (.let₁ .unit (.inl .unit)) (.case (.op (.let₁ .bv .bv)) (.inl .bv) (.inr (bitDeriv b)))

private theorem leftTyped : HasTypeEffect Γ₀ .nil loopL U strict :=
  ⟨leftDeriv.toHasType, .iter rfl bot_le (sup_le le_rfl bot_le)⟩

private theorem rightTyped (b : Bool) : HasTypeEffect Γ₀ .nil (loopR b) U strict := by
  refine ⟨(rightDeriv b).toHasType, ?_⟩
  cases b <;> exact .iter rfl (sup_le bot_le bot_le)
    (sup_le (sup_le le_rfl (sup_le bot_le bot_le)) (sup_le bot_le bot_le))

private theorem visible : ¬ IsPure (⊥ : Eff) () := by
  change strict ≠ ⊥
  decide

private def noPure : PureMaps (Φ := Unit) (ε := Eff) V := fun i h => by
  cases i
  exact (visible h).elim

private noncomputable def obsL : ITree.Tree (Event (Φ := Unit) V) (D U) :=
  leftDeriv.denote D (instructions V noPure) (fun x => x.elim) (fun i => i.elim0)

private noncomputable def obsR (b : Bool) : ITree.Tree (Event (Φ := Unit) V) (D U) :=
  (rightDeriv b).denote D (instructions V noPure) (fun x => x.elim) (fun i => i.elim0)

private theorem observe_left : obsL = leftTable.run PUnit.unit := by
  unfold obsL leftDeriv
  erw [Derivation.denote]
  simp only [Derivation.denote, pure_bind, Machine.run]
  congr 1
  funext state
  change ((instructions V noPure).eval () (code false) >>= fun r => pure r) = leftTable.step state
  rw [eval_bind_of_not_pure V noPure visible]
  rfl

private theorem denote_bit {n : Nat} {β : BoundCtx (Ty Unit) n} (b : Bool)
    (γ : FreeEnv D Γ₀) (ρ : BoundEnv D β) :
    (bitDeriv b).denote D (instructions V noPure) γ ρ = pure (code b) := by
  cases b <;> simp [bitDeriv, Derivation.denote, code] <;> rfl

private theorem observe_right (b : Bool) : obsR b = (rightTable b).run (code false) := by
  unfold obsR rightDeriv
  erw [Derivation.denote]
  simp only [Derivation.denote, pure_bind, BoundEnv.snoc_zero, Machine.run]
  change Silmaril.Elgot.iter _ (code false) = Silmaril.Elgot.iter _ (code false)
  congr 1
  funext state
  rw [eval_bind_of_not_pure V noPure visible, ITree.vis_bind]
  change ITree.vis _ _ = (rightTable b).step state
  unfold Machine.step
  congr 1
  funext r
  cases r with
  | inl v =>
      change (ITree.ret (E := Event (Φ := Unit) V) (Sum.inl PUnit.unit : D U ⊕ D Bit) >>= pure) = _
      rw [show ITree.ret (E := Event (Φ := Unit) V) (Sum.inl PUnit.unit : D U ⊕ D Bit) =
        pure (Sum.inl PUnit.unit : D U ⊕ D Bit) from rfl, pure_bind]
      rfl
  | inr v =>
      let emptyEnv : BoundEnv D (.nil : BoundCtx (Ty Unit) 0) := fun i => i.elim0
      let ρ : BoundEnv D ((BoundCtx.nil.snoc Bit).snoc U) := (emptyEnv.snoc state).snoc PUnit.unit
      change (((bitDeriv b).denote D (instructions V noPure) (fun x => x.elim) ρ >>=
        fun next => pure (Sum.inr next : D U ⊕ D Bit)) >>= pure) = ITree.ret (Sum.inr (code b))
      rw [denote_bit, pure_bind, pure_bind]
      rfl

private abbrev squareL : Expr Unit :=
  .case (.op () (.inl .unit)) (.inl (.var 0)) (.inr (.inl .unit))

private abbrev squareR (b : Bool) : Expr Unit :=
  .case (.op () (.let₁ (.inl .unit) (.var 0))) (.inl (.var 0)) (.inr (bit b))

private theorem written_square {b : Bool} (observed : obsL = obsR b) :
    Eqv Δ (.coprod U Bit) strict squareL (squareR b) := by
  have sameState := repeat_code_of_observation (observe_left.symm.trans (observed.trans (observe_right b)))
  subst b
  have initial : Wf Δ (.inl .unit : Expr Unit) Bit (⊥ : Eff) := .inl (.unit _ _)
  have value : Wf ((Bit, ⊥) :: Δ) (.var 0 : Expr Unit) Bit strict := .var 0 bot_le
  have beta : Eqv Δ Bit strict (.let₁ (.inl .unit) (.var 0)) (.inl .unit) :=
    .step (.let1_beta initial value)
  exact .case (.op le_rfl beta.symm) (.refl (.inl (.var 0 bot_le))) (.refl (.inr (.inl (.unit _ _))))

private theorem native_reflection {b : Bool} (observed : obsL = obsR b) :
    AbortEquiv (⊥ : Eff) Γ₀ .nil loopL (loopR b) U := by
  apply replay_written_square (Γ := Γ) (A := U) (A' := Bit) (C := U)
    (a := .unit) (h := nativeEmbed) (b := bodyL) (b' := bodyR b)
    .unit (.inl .unit) (.inl .unit) (.op (.inl .unit))
    (.case (.op (.let₁ .bv .bv)) (.inl .bv) (.inr (bitDeriv b).toHasType)) rfl ?_ (written_square observed)
  cases b <;> rfl

-- Matching weak observations reflect to the native equation at strict on
-- both sides. The independently written step terms are compared by beta.
example {b : Bool} (observed : obsL = obsR b) :
    HasTypeEffect Γ₀ .nil loopL U strict ∧ HasTypeEffect Γ₀ .nil (loopR b) U strict ∧
      repairedDenoteInSyntax (⊥ : Eff) leftDeriv = repairedDenoteInSyntax (⊥ : Eff) (rightDeriv b) :=
  ⟨leftTyped, rightTyped b, (repairedDenoteInSyntax_eq_iff (⊥ : Eff) _ _).mpr (native_reflection observed)⟩

example : obsL = obsR false :=
  observe_left.trans ((runs_eq right_commutes PUnit.unit).trans (observe_right false).symm)

example : obsL ≠ obsR true := fun eq =>
  Bool.noConfusion (repeat_code_of_observation (observe_left.symm.trans (eq.trans (observe_right true))))

example {b : Bool} :
    repairedDenoteInSyntax (⊥ : Eff) leftDeriv = repairedDenoteInSyntax (⊥ : Eff) (rightDeriv b)
      ↔ b = false := by
  refine ⟨fun packed => ?_, fun h => ?_⟩
  · have native := (repairedDenoteInSyntax_eq_iff (⊥ : Eff) leftDeriv (rightDeriv b)).mp packed
    have eq : obsL = obsR b := sound V noPure native leftDeriv (rightDeriv b) (fun i => i.elim0)
    exact repeat_code_of_observation (observe_left.symm.trans (eq.trans (observe_right b)))
  · subst b
    have eq := observe_left.trans ((runs_eq right_commutes PUnit.unit).trans (observe_right false).symm)
    exact (repairedDenoteInSyntax_eq_iff (⊥ : Eff) leftDeriv _).mpr (native_reflection eq)

example : strict < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

-- The behavior at the unreachable right-tag state can differ even when the
-- same initial observations agree. This defeats a global uniformity map.
private def extraReturn : Machine V () (D Bit) (D U) :=
  ⟨toSmall V Bit, fun s r => match s with
    | .inl _ => (rightTable false).reply s r
    | .inr _ => .inl PUnit.unit⟩

example : extraReturn.run (code false) = (rightTable false).run (code false) ∧
    ¬ ∃ h, Commutes extraReturn (rightTable false) h := by
  have commuteLeft : Commutes leftTable extraReturn embed := by
    intro s
    refine ⟨rfl, fun r => ?_⟩
    cases r <;> rfl
  refine ⟨(runs_eq commuteLeft PUnit.unit).symm.trans (runs_eq right_commutes PUnit.unit), ?_⟩
  rintro ⟨h, comm⟩
  have forced : code true = h (code true) := (toSmall V Bit).injective (comm (code true)).1
  have wrongReply := (comm (code true)).2 (.inr PUnit.unit)
  rw [← forced] at wrongReply
  cases wrongReply

end LetIterObservedFeedbackFixture

namespace LetIterFiniteFeedbackReplayFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

private abbrev Bit := Code.sum .unit .unit
private abbrev Three := Code.sum Bit .unit
private abbrev Ops := Opcode Three Bit
private abbrev Eff := Bool × Bool
private abbrev strict : Eff := (true, false)

local instance : HasEff Ops Eff := ⟨fun _ => strict⟩
local instance : EffectIteration Eff := EffectIteration.complete Eff

private abbrev off : Bit.Value := .inl PUnit.unit
private abbrev on : Bit.Value := .inr PUnit.unit

private def encode (s : Bit.Value) : Three.Value := .inl s

private def toggle (s : Bit.Value) : Bit.Value :=
  match s with
  | .inl _ => on
  | .inr _ => off

private def rightNext (t : Three.Value) : Three.Value :=
  match t with
  | .inl s => .inl (toggle s)
  | .inr _ => .inr PUnit.unit

private def left : Table Three Bit Bit .unit where
  request := encode
  reply s
    | .inl _ => .inl PUnit.unit
    | .inr _ => .inr (toggle s)

private def right : Table Three Bit Three .unit where
  request := id
  reply t
    | .inl _ => .inl PUnit.unit
    | .inr _ => .inr (rightNext t)

private theorem commute : Commutes left right encode := by
  intro s
  refine ⟨rfl, ?_⟩
  intro r
  cases r <;> rfl

private theorem allReach (s : Bit.Value) : left.Reaches off s := by
  cases s with
  | inl u =>
      cases u
      exact .initial
  | inr u =>
      cases u
      exact .after_reply .initial on rfl

private theorem initialObs : left.run off = right.run (encode off) :=
  runs_eq commute off

-- The recovered map distinguishes two live states. Neither state is a dead row.
example : ∃ h, Commutes left right h ∧ h off ≠ h on ∧
    ∀ s, Eqv ([] : EffectCtx (Ty Unit) Eff) Three.ty strict
      ((stateMap Bit Three h : Expr Ops).subst (Bit.literal s).subst0) (Three.literal (encode s)) := by
  obtain ⟨h, square, _⟩ := exists_commutes_of_initial (fun _ _ eq => eq) allReach initialObs
  have table (s : Bit.Value) : h s = encode s := (square s).1.symm
  refine ⟨h, square, ?_, fun s => ?_⟩
  · rw [table off, table on]
    intro eq
    cases Sum.inl.inj eq
  · rw [← table s]
    exact stateMap_readback h s

-- A repeat changes the visible state on both machines. The returning reply
-- exits at either state. The initial equality above replays at strict.
example :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (Bit.literal off).toLetIter 0 = some a ∧
      (Three.literal (encode off)).toLetIter 0 = some a' ∧
      left.source.toLetIter 1 = some b ∧ right.source.toLetIter 1 = some b' ∧
      HasTypeEffect (Ctx.nil : Ctx Empty (Ty Unit)) .nil (.iter a b) Ty.unit strict ∧
      HasTypeEffect (Ctx.nil : Ctx Empty (Ty Unit)) .nil (.iter a' b') Ty.unit strict ∧
      AbortEquiv (⊥ : Eff) (Ctx.nil : Ctx Empty (Ty Unit)) .nil (.iter a b) (.iter a' b') Ty.unit :=
  replay (fun _ _ eq => eq) allReach initialObs le_rfl rfl

example : strict < (⊤ : Eff) :=
  lt_of_le_of_ne le_top (fun h => Bool.noConfusion (congrArg Prod.snd h))

end LetIterFiniteFeedbackReplayFixture
