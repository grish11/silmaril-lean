module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Interface.Defs

/-! # Shared caller refinement on a fixed carrier -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open ScheduleSearch (StateInventory)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {states : Nat}

structure EntryCounterexample (Φ : Type u) [HasTy Φ Syntax.Ty] (A : Syntax.Ty) (states : Nat) where
  input : Syntax.Payload A
  initial : Fin states
  script : List (InterpreterScript.Row Φ states)

/-- The same total interpreter runs both independently decoded endpoints. -/
def EntryCounterexample.interpreter [DecidableEq Φ] (w : EntryCounterexample Φ A states) :
    Syntax.Primitives Φ states :=
  InterpreterScript.interpret w.script

inductive EntryVerdict (Φ : Type u) [HasTy Φ Syntax.Ty] (A : Syntax.Ty) (states : Nat) where
  | refines
  | counterexample (witness : EntryCounterexample Φ A states)

variable [DecidableEq Φ]

/-- Use one support for the whole shared domain, including both typed
decodings at every representative. -/
def Table.entryQueries (g : Table S R) (h : Table S T) (callers : CallerEnumeration A)
    (decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry))
    (decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) : List (InterpreterScript.Query Φ states) :=
  (callers.packets.flatMap fun input =>
    g.queries (decodeLeft input) left stores ++ h.queries (decodeRight input) right stores).dedup

/-- Enumerate the restrictions once and use them with the existing bounded
native runners. Return the first failing caller in the supplied order. -/
def Table.findEntryFailure (g : Table S R) (h : Table S T)
    (callers : CallerEnumeration A)
    (decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry))
    (decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) : Option (EntryCounterexample Φ A states) :=
  let scripts := InterpreterScript.assignments replies stores
    (g.entryQueries h callers decodeLeft decodeRight left right stores)
  callers.packets.findSome? fun input =>
    let a := decodeLeft input
    let b := decodeRight input
    scripts.findSome? fun script =>
      let prim := InterpreterScript.interpret script
      let failure := stores.values.find? fun s =>
        !decide ((g.runFinite a prim left stores ⟨g.entry, a⟩ s).refines
          (h.runFinite b prim right stores ⟨h.entry, b⟩ s))
      failure.map fun s => ⟨input, s, script⟩

/-- Exact readback gates both original CFGs, including at an empty shared
domain. A checked empty domain yields the vacuous positive verdict. -/
def Table.compareEntries? (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry))
    (decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) : Option (EntryVerdict Φ A states) :=
  if g.checkNative raw && h.checkNative raw' then
    some (match g.findEntryFailure h callers decodeLeft decodeRight replies left right stores with
      | none => .refines
      | some witness => .counterexample witness)
  else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
