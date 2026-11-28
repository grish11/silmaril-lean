module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Defs

/-! # Translation of normalized two-request rows with one original state -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion)
open CategoryTheory

/-- A finite row has a typed active input. A call replaces that input by
its reply, and a constructor case replaces it by its selected payload. -/
inductive Step (F : Family n) : Code → Code → Type
  | lit {I O : Code} : O.Value → Step F I O
  | call {I O : Code} (f : Opcode F) : f.argCode.Value → Step F f.replyCode O → Step F I O
  | split {L R O : Code} : Step F L O → Step F R O → Step F (.sum L R) O

def value : (c : Code) → c.Value → Tm Ops
  | .unit, _ => .unit
  | .sum l _, .inl x => .inl (value l x)
  | .sum _ r, .inr x => .inr (value r x)

variable {I J O P : Code}

def Step.source : {I : Code} → Step F I O → Expr Ops
  | _, .lit x => O.literal x
  | _, .call f x k => .let₁ (.op f (f.argCode.literal x)) k.source
  | _, .split l r => .case (.var 0) l.source r.source

def Step.ssa : {I : Code} → Step F I O → Region Ops
  | _, .lit x => .br 0 (value O x)
  | _, .call f x k => .let₁ (.op f (value f.argCode x)) k.ssa
  | _, .split l r => .case (.var 0) l.ssa r.ssa

theorem value_typed : (c : Code) → (x : c.Value) → (Γ : VCtx (Ty Unit)) →
    Tm.BranchValue Γ (value c x : Tm Ops) c.ty
  | .unit, _, _ => .unit
  | .sum l _, .inl x, Γ => .inl (value_typed l x Γ)
  | .sum _ r, .inr x, Γ => .inr (value_typed r x Γ)

/-- The translated region branches at the exact result type. The row
can be placed under additional captured values. -/
theorem Step.typed : {I : Code} → (s : Step F I O) → (Γ : VCtx (Ty Unit)) →
    Region.ValueBranches (I.ty :: Γ) s.ssa [O.ty]
  | I, .lit x, Γ => .br rfl (value_typed O x (I.ty :: Γ))
  | I, .call f x k, Γ => .let₁ (.op (value_typed f.argCode x (I.ty :: Γ)).hasType) (typed k _)
  | .sum L R, .split l r, Γ => .case (.var rfl) (typed l ((Code.sum L R).ty :: Γ)) (typed r ((Code.sum L R).ty :: Γ))

/-- Expand a finite code by case splits with a typed row at each leaf. -/
def tabulate : (c : Code) → (c.Value → Step F .unit O) → Step F c O
  | .unit, rows => rows PUnit.unit
  | .sum l r, rows => .split (tabulate l (fun v => rows (.inl v))) (tabulate r (fun v => rows (.inr v)))

def literals (c : Code) (f : c.Value → O.Value) : Step F c O :=
  tabulate c (fun v => .lit (f v))

def row (r : Row F J O) (c : Code) : Step F c (.sum O J) :=
  match r with
  | .ret b => .lit (.inl b)
  | .call f x k => .call f x (literals f.replyCode k)

def Step.mapOut (f : O.Value → P.Value) : {I : Code} → Step F I O → Step F I P
  | _, .lit x => .lit (f x)
  | _, .call op a k => .call op a (mapOut f k)
  | _, .split l r => .split (mapOut f l) (mapOut f r)

def plans (first : Ops) (argument : first.argCode.Value) (next : first.replyCode.Value → Row F U O) :
    Plans F U O :=
  fun _ => .two first argument next

def replyStep (first : Ops) (next : first.replyCode.Value → Row F U O) :
    Step F first.replyCode (.sum O U) :=
  tabulate first.replyCode (fun r => row (next r) U)

def fused (first : Ops) (argument : first.argCode.Value) (next : first.replyCode.Value → Row F U O) :
    Step F U (.sum O U) :=
  .call first argument (replyStep first next)

def expanded (first : Ops) (argument : first.argCode.Value) (next : first.replyCode.Value → Row F U O) :
    Step F (.sum U first.replyCode) (.sum O (.sum U first.replyCode)) :=
  .split (.call first argument (literals first.replyCode (fun v => .inr (.inr v))))
    (Step.mapOut (O := .sum O U) (P := .sum O (.sum U first.replyCode)) (Sum.map id Sum.inl)
      (replyStep first next))

abbrev NTm (F : Family n) (m : Nat) := Silmaril.Isotope.LetIter.LocallyNameless.Tm Empty (Opcode F) m

def nativeValue (m : Nat) : (c : Code) → c.Value → NTm F m
  | .unit, _ => .unit
  | .sum l _, .inl x => .inl (nativeValue m l x)
  | .sum _ r, .inr x => .inr (nativeValue m r x)

def Step.native : {I : Code} → Step F I O → (m : Nat) → NTm F (m+1)
  | _, .lit x, m => nativeValue (m+1) O x
  | _, .call f x k, m => .let₁ (.op f (nativeValue (m+1) f.argCode x)) (k.native (m+1))
  | _, .split l r, m => .case (.bv 0) (l.native (m+1)) (r.native (m+1))

def eraseValue : {m : Nat} → NTm F m → Option (Tm Ops)
  | _, .bv i => some (.var i.val)
  | _, .unit => some .unit
  | _, .inl a => (eraseValue a).map .inl
  | _, .inr a => (eraseValue a).map .inr
  | _, .op f a => (eraseValue a).map (.op f)
  | _, _ => none

def eraseStep : {m : Nat} → NTm F m → Option (Region Ops)
  | _, .let₁ a k => return .let₁ (← eraseValue a) (← eraseStep k)
  | _, .case a l r => return .case (← eraseValue a) (← eraseStep l) (← eraseStep r)
  | _, a => (eraseValue a).map (.br 0)

def eraseLoop (state : Code) : NTm F 0 → Option (Region Ops)
  | .iter a b => do
    let init ← eraseStep a
    let body ← eraseStep b
    pure (Region.compLSubst (fun _ => init) (fun _ => iterateRegion state.ty body) 0)
  | _ => none

def loopCFG (s : Step F I (.sum O I)) (v : I.Value) : Region Ops :=
  Region.compLSubst (fun _ => .br 0 (value I v)) (fun _ => iterateRegion I.ty s.ssa) 0

def fusedNative (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) : NTm F 0 :=
  .iter .unit ((fused f x k).native 0)

def expandedNative (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) : NTm F 0 :=
  .iter (.inl .unit) ((expanded f x k).native 0)

/-- The ordered-pair seed over the same opcode family as the native rows. -/
abbrev targetSeed {ε : Type} [HasEff (Opcode F) ε] (pe : ε) :=
  JoinedStep (τ := Ty Unit) (Φ := Ops) pe

/-- The exact singleton arrow of the translated row. -/
noncomputable def Step.arrow {ε : Type} [HasEff (Opcode F) ε] (pe : ε) (s : Step F I O) :
    Extension.Singleton.ofType (targetSeed (F := F) pe) I.ty ⟶
      Extension.Singleton.ofType (targetSeed (F := F) pe) O.ty :=
  Extension.Singleton.ofRegion (targetSeed pe) (s.typed [])

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
