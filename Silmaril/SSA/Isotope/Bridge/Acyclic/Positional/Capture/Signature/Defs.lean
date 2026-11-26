module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Signature.Thms

/-! # Relabelling captured tables and their exact result grammar -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Morphism (SignatureMap)
open Institution (InstrSig)
open Institution.Acyclic (mapContextLookup)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {L : LCtx τ} {d k n : Nat} {β : BoundCtx τ d} {R : Fin k → τ} {A : τ}

/-- Keep the same local or outward position when its payload type changes. -/
def Target.mapTypes (f : τ → υ) : Target R L A → Target (f ∘ R) (L.map f) (f A)
  | .local i => .local i
  | .exit h => .exit (mapContextLookup f h)

def Block.mapSignature (b : Block P.Instr β R L A) :
    Block Q.Instr (β.mapTypes g.ty) (g.ty ∘ R) (L.map g.ty) (g.ty A) :=
  match b with
  | .jump a t => .jump (a.mapSignature g) (t.mapTypes g.ty)
  | .case (B := B) (D := D) a l r =>
    .case ((a.mapSignature g).castResult (SignatureMap.PreservesSums.coprod (g := g) B D))
      (l.mapTypes g.ty) (r.mapTypes g.ty)

def Table.mapSignature (p : Table P.Instr β L n) :
    Table Q.Instr (β.mapTypes g.ty) (L.map g.ty) n :=
  ⟨g.ty ∘ p.types, fun i => (p.block i).mapSignature g⟩

def Scope.mapTypes (f : τ → υ) :
    {m : Nat} → {γ : BoundCtx τ m} → Scope β γ → Scope (β.mapTypes f) (γ.mapTypes f)
  | _, _, .base => .base
  | _, _, .skip s A => .skip (s.mapTypes f) (f A)

namespace Reverse

mutual

def Tree.mapSignature {A : τ} (t : Tree P.Instr β L A) :
    Tree Q.Instr (β.mapTypes g.ty) (L.map g.ty) (g.ty A) :=
  match t with
  | .jump a k => .jump (a.mapSignature g) (Edge.mapSignature k)
  | .case (B := B) (D := D) a l r =>
    .case ((a.mapSignature g).castResult (SignatureMap.PreservesSums.coprod (g := g) B D))
      (Edge.mapSignature l) (Edge.mapSignature r)
termination_by structural t

def Edge.mapSignature {A : τ} (e : Edge P.Instr β L A) :
    Edge Q.Instr (β.mapTypes g.ty) (L.map g.ty) (g.ty A) :=
  match e with
  | .exit h => .exit (mapContextLookup g.ty h)
  | .local t => .local (Tree.mapSignature t)
termination_by structural e

end

/-- Map the grammar witness constructor by constructor, retaining the exact
entry binder, branch binders, and indexed outward returns. -/
def Program.mapSignature (p : Program P.Instr β L) :
    Program Q.Instr (β.mapTypes g.ty) (L.map g.ty) :=
  ⟨g.ty p.input, p.entry.mapSignature g, p.body.mapSignature g⟩

end Reverse
end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
