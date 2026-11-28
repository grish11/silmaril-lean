module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Defs

/-! # Typed acyclic control for finite reply rows -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory (returnRegion)
open Extension.Singleton (projectStep)

universe u v

variable {Φ : Type} [Profile Φ]

abbrev nativeShape (Φ : Type) [Profile Φ] (s : ReplyShape) : Native Φ :=
  Paper.TypeCategory.ofType s.ty

/-- A path through the sum constructors, forwarding the residual Unit variable. -/
noncomputable def point (s : ReplyShape) : s.Value → (nativeUnit Φ ⟶ nativeShape Φ s) :=
  match s with
  | .empty => PEmpty.elim
  | .unit => fun _ => 𝟙 _
  | .sum l r => fun
    | .inl x => point l x ≫ (Paper.TypeCategory.sumCofan l.ty r.ty).inl
    | .inr x => point r x ≫ (Paper.TypeCategory.sumCofan l.ty r.ty).inr

/-- Acyclic control with one live payload. A let sequences a typed producer
and its sequel, so case arms can share the sequel. -/
inductive Control (Φ : Type) [Profile Φ] : ReplyShape → ReplyShape → Type where
  | forward (s : ReplyShape) : Control Φ s s
  | inl (l r : ReplyShape) : Control Φ l (.sum l r)
  | inr (l r : ReplyShape) : Control Φ r (.sum l r)
  | call (op : Φ) : Control Φ .unit (Profile.reply op)
  | let₁ {s t u : ReplyShape} (producer : Control Φ s t) (sequel : Control Φ t u) : Control Φ s u
  | case {l r t : ReplyShape} (left : Control Φ l t) (right : Control Φ r t) : Control Φ (.sum l r) t
  | empty (t : ReplyShape) : Control Φ .empty t

/-- The written guarded region. Composition substitutes the sequel for the
producer's return label, weakening binders along the way. -/
def Control.region {s t : ReplyShape} : Control Φ s t → Region Φ
  | .forward _ => .br 0 (.var 0)
  | .inl _ _ => .br 0 (.inl (.var 0))
  | .inr _ _ => .br 0 (.inr (.var 0))
  | .call p => returnRegion (.op p (.var 0))
  | .let₁ producer sequel => compLSubst (fun _ => producer.region) (fun _ => sequel.region) 0
  | .case left right =>
      .case (.var 0) (left.region.renameVars (lift Nat.succ)) (right.region.renameVars (lift Nat.succ))
  | .empty _ => returnRegion (.abort (.var 0))

/-- The original control arrow in standard Paper. -/
noncomputable def Control.native {s t : ReplyShape} : Control Φ s t →
    (nativeShape Φ s ⟶ nativeShape Φ t)
  | .forward _ => 𝟙 _
  | .inl l r => (Paper.TypeCategory.sumCofan l.ty r.ty).inl
  | .inr l r => (Paper.TypeCategory.sumCofan l.ty r.ty).inr
  | .call p => Paper.TypeCategory.primitiveReturn p
  | .let₁ producer sequel => producer.native ≫ sequel.native
  | .case (l := l) (r := r) left right =>
      (Paper.TypeCategory.sumIso l.ty r.ty).hom ≫ coprod.desc left.native right.native
  | .empty _ => Paper.TypeCategory.emptyIsInitial.to _

/-- Replace each returned value by the following finite row. -/
def thenRow {α : Type u} {β : Type v} (next : α → Row Φ β) : Row Φ α → Row Φ β
  | .leaf a => next a
  | .call p k => .call p (fun x => thenRow next (k x))

/-- Read back the control from an exact typed input, substituting a shared
sequel into the successful leaves of its producer. -/
def Control.readback {s t : ReplyShape} : Control Φ s t → s.Value → Row Φ t.Value
  | .forward _, x => .leaf x
  | .inl _ _, x => .leaf (.inl x)
  | .inr _ _, x => .leaf (.inr x)
  | .call p, _ => .call p .leaf
  | .let₁ producer sequel, x => thenRow sequel.readback (producer.readback x)
  | .case left _, .inl x => left.readback x
  | .case _ right, .inr x => right.readback x
  | .empty _, x => nomatch x

/-- An acyclic producer followed by typed terminal jumps. -/
structure Program (Φ α : Type) [Profile Φ] where
  output : ReplyShape
  body : Control Φ .unit output
  jump : output.Value → α

noncomputable def Program.native {α : Type} {Y : Native Φ} (p : Program Φ α)
    (leaf : α → (nativeUnit Φ ⟶ Y)) : nativeUnit Φ ⟶ Y :=
  p.body.native ≫ dispatch p.output (fun x => leaf (p.jump x))

def Program.readback {α : Type} (p : Program Φ α) : Row Φ α :=
  thenRow (fun x => .leaf (p.jump x)) (p.body.readback PUnit.unit)

/-- The source built from the original native control arrows. -/
noncomputable def sourceStep (l r : Program Φ Route) : unitObj Φ ⨿ unitObj Φ ⟶
    unitObj Φ ⨿ (unitObj Φ ⨿ unitObj Φ) :=
  coprod.desc (projectRow (l.native nativeRoute)) (projectRow (r.native nativeRoute))

/-- The target built from the original native control arrow. -/
noncomputable def targetStep (p : Program Φ Bool) : unitObj Φ ⟶ unitObj Φ ⨿ unitObj Φ :=
  projectStep (Seed Φ) (p.native nativeTarget)

namespace Example

abbrev Op := FiniteReplies.Example.Op
abbrev Bit : ReplyShape := .sum .unit .unit
abbrev Reply : ReplyShape := .sum .unit Bit

/-- Inspect the ternary reply. The middle branch makes a second request,
and every successful branch reconstructs its original reply tag. -/
def routeReply : Control Op Reply Reply :=
  .case (.inl .unit Bit) (.case
    (.let₁ (.call .tick) (.let₁ (.inl .unit .unit) (.inr .unit Bit)))
    (.let₁ (.inr .unit .unit) (.inr .unit Bit)))

/-- The original producer installs an administrative tag before entering a
case with one impossible arm and a shared effectful sequel. -/
def producer : Control Op .unit Reply :=
  .let₁ (.call .select)
    (.let₁ (.inr .empty Reply) (.case (.empty Reply) routeReply))

def targetProducer : Control Op .unit Reply :=
  .let₁ (.call .select) routeReply

def left : Program Op Route :=
  ⟨Reply, producer, fun
    | .inl _ => .first
    | .inr (.inl _) => .second
    | .inr (.inr _) => .exit⟩

def right : Program Op Route :=
  ⟨Reply, producer, fun
    | .inl _ => .second
    | .inr (.inl _) => .first
    | .inr (.inr _) => .exit⟩

def target : Program Op Bool :=
  ⟨Reply, targetProducer, fun
    | .inl _ | .inr (.inl _) => true
    | .inr (.inr _) => false⟩

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic
