module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Defs

/-! # Finite reply trees with typed ordered exits -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits

open Kleisli (value)
open LambdaSSA (At Ren)
open LambdaSSA.Acyclic (Operand FiniteExit)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (labelAt_get)
open LetIter.Semantics.Categorical (boundEnv)

/-- A successful leaf names its position even when several positions have
the same payload type and value. -/
abbrev Exit (L : List Sorts) := Σ i : Fin L.length, value (L.get i)

/-- Interpret a positional injection in the structural free-type model. -/
def packAt (L : List Sorts) (i : Nat) {A : Sorts} (h : At L i A) (x : value A) :
    value (packedExitType L) :=
  match L, i with
  | [], _ => nomatch h
  | B :: _, 0 =>
    let e : B = A := Option.some.inj h
    .inl (e.symm ▸ x)
  | _ :: L, i + 1 => .inr (packAt L i h x)

def Exit.packed {L : List Sorts} (x : Exit L) : value (packedExitType L) :=
  packAt L x.1 (labelAt_get L x.1) x.2

/-- Quote a closed structural payload into any bound context. -/
def literal {n : Nat} (β : BoundCtx Sorts n) :
    (A : Sorts) → value A → Operand signature.Instr β A
  | .base a, _ => a.elim
  | .empty, x => x.elim
  | .unit, _ => ⟨.unit, .unit⟩
  | .product A B, (a, b) =>
    let p := literal β A a
    let q := literal β B b
    ⟨.pair p.1 q.1, .pair p.2 q.2⟩
  | .coprod A _, .inl a =>
    let p := literal β A a
    ⟨.inl p.1, .inl p.2⟩
  | .coprod _ B, .inr b =>
    let p := literal β B b
    ⟨.inr p.1, .inr p.2⟩

def exitOperand (L : List Sorts) : ReturnOperand (Exit L) (packedExitType L) :=
  fun β x => FiniteExit.tag L x.1 (labelAt_get L x.1) (literal β _ x.2)

/-- The shared continuation dispatches the entry result to its original
native position. The empty tail has no value to pass to the fallback. -/
def router {Φ : Type} [HasTy Φ Sorts] {k : Nat} {β : BoundCtx Sorts k}
    {K : List Sorts} {j : Nat} {D : Sorts} (fallback : At K j D) :
    (L : List Sorts) → {ρ : Nat → Nat} → Ren L K ρ →
    LambdaSSA.Acyclic.Positional.Capture.Reverse.Tree Φ β K (packedExitType L)
  | [], _, _ => .jump ⟨.abort (.bv 0), .abort .bv⟩ (.exit fallback)
  | A :: L, ρ, ren =>
    .case ⟨.bv 0, .bv⟩ (.exit (ren (rfl : At (A :: L) 0 A)))
      (.local (router fallback L (ρ := fun i => ρ (i + 1)) (fun _ _ h => ren h)))

/-- Capture the computation, then route the result at the actual ordered
outward interface. The interface has a head for the impossible empty tail. -/
def program (H : Sorts) (L : List Sorts) (p : Tree (Exit (H :: L))) :
    Program signature.Instr .nil (H :: L) :=
  ⟨packedExitType (H :: L), p.operandWith (exitOperand (H :: L)) .nil,
    router (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))⟩

def equation (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) : GrammarEquation signature :=
  ⟨⟨0, .nil, H :: L⟩, program H L p, program H L q⟩

noncomputable def programOutcomes (H : Sorts) (L : List Sorts) (p : Tree (Exit (H :: L))) :
    Set (Outcome (value (packedExitType (H :: L)))) :=
  (Kleisli.run model (program H L p).toLetCase.2 (boundEnv value (β := .nil) PUnit.unit)).outcomes

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits
