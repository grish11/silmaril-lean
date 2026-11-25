module

import Silmaril.Semantics.ITree.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

/-! A mixed weak interaction-tree model and original-bound endpoint reflection
for the open unary source fragment. -/

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

end LetIterResponseSingleCall
