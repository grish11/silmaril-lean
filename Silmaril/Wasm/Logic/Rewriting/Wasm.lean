module

public import Silmaril.Logic.Rewriting.Reachability
public import Silmaril.Wasm.Logic.Reachability

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Rewriting.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
variable {H : Type}

/-- Constants name the actual initial and final configurations, with no arithmetic
or operational axioms hidden in their interpretations. -/
inductive Operation : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | initial : Operation 0 (fun _ => ()) ()
  | final : Operation 0 (fun _ => ()) ()

def signature : Algebraic.ManySorted.Signature Unit := ⟨Operation⟩

def model (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) : InhabitedModel signature where
  model :=
    { algebra :=
        { carrier := fun _ => Config H
          operation op _ := match op with
            | .initial => Reachability.Wasm.start s f vs a b
            | .final => Reachability.Wasm.finish s f vs }
      reaches _ := Steps P host
      refl _ _ := .refl
      trans _ := Relation.ReflTransGen.trans
      congruence op _ _ _ := by cases op <;> exact .refl }
  nonempty _ := ⟨Reachability.Wasm.finish s f vs⟩

def twoDrop : Algebraic.ManySorted.Equation signature :=
  ⟨0, (fun _ => ()), (), .app .initial (fun i => i.elim0), .app .final (fun i => i.elim0)⟩

/-- Directed rewriting is precisely actual pinned Core `Steps`, not a new machine. -/
theorem rewriting_iff_execution (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) :
    Sentence.Satisfies (model P host s f vs a b).model (.rewrite twoDrop) ↔
      Steps P host (Reachability.Wasm.start s f vs a b) (Reachability.Wasm.finish s f vs) := by
  constructor
  · intro h
    exact h (fun i => i.elim0)
  · intro h _
    exact h

theorem twoDrop_rewrites (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) :
    Sentence.Satisfies (model P host s f vs a b).model (.rewrite twoDrop) := by
  apply (rewriting_iff_execution P host s f vs a b).mpr
  exact (Relation.ReflTransGen.single (Reachability.Wasm.first_step P host s f vs a b)).tail
    (Reachability.Wasm.second_step P host s f vs a)

/-- This reaches the independent actual finite reachability sentence in the
canonical matching model; its designated step is the already closed `Steps`. -/
theorem twoDrop_canonical (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) :
    CanonicalSentence.Satisfies (model P host s f vs a b) (compile (.rewrite twoDrop)) :=
  (compile_satisfaction _ _).mpr (twoDrop_rewrites P host s f vs a b)

theorem twoDrop_matching (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) :
    Matching.FixedPoint.Sentence.Satisfies (reachModel (model P host s f vs a b) () true)
      (Reachability.encode () (compileEquation twoDrop)) :=
  (Reachability.encode_correct _ _).mpr (twoDrop_canonical P host s f vs a b)

end Silmaril.Logic.Rewriting.Wasm
