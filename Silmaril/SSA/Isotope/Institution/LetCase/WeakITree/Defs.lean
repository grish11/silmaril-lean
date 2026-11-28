module

public import Silmaril.SSA.Isotope.Institution.LetCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Institution.Thms
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Monadic

/-! # Weak interaction trees as models of exact LetCase equations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.LetCase.WeakITree

open CategoryTheory
open Silmaril.Logic.Metatheory.TheoryModel (Algebra)
open Isotope.Theory (TypingIndex)
open Isotope.LetCase.LocallyNameless
open Isotope.Semantics (BoundEnv)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u

variable {κ : Type (u + 1)} [AtomValues κ] {Events : Type u → Type u}

local notation "D" => Ty.denote (AtomValues.carrier (κ := κ))

/-- The empty free-name context at the universe of the exact institution. -/
abbrev emptyContext {κ : Type (u + 1)} : Ctx (ULift.{u+1} Empty) (Ty κ) := .nil

local notation "Γ₀" => (emptyContext (κ := κ))

/-- View the same instructions, types and effects as an exact LetCase signature. -/
def signature (P : FlatInstitution.Signature.{u, u+1} κ) :
    InstrSig.{u+1} (Ty κ) (ULift.{u+1} Bool) where
  Instr := P.Instr
  hasTy := P.hasTy
  hasEff := ⟨fun f => ⟨instrEff (ε := Bool) f⟩⟩

/-- An effect-identity map is an instruction relabelling of the exact
LetCase institution. -/
def signatureHom {P Q : FlatInstitution.Signature.{u, u+1} κ} (g : P ⟶ Q)
    (effects : g.toSignatureMap.eff = id) : signature P ⟶ signature Q where
  instr := g.toSignatureMap.instr
  source f := (g.toSignatureMap.source f).trans (congrFun g.types _)
  target f := (g.toSignatureMap.target f).trans (congrFun g.types _)
  effect f := congrArg ULift.up ((g.toSignatureMap.effect f).trans (congrFun effects _))

/-- The existing exact LetCase room at these instructions and empty named context. -/
abbrev equationRoom (P : FlatInstitution.Signature.{u, u+1} κ) :=
  (LetCase.inst Γ₀).obj (signature P)

/-- The existing exact LetCase equation carrier. -/
abbrev Equation (P : FlatInstitution.Signature.{u, u+1} κ) := (equationRoom P).Sen

/-- Present an operand with no free names at the universe of the exact institution.
Only the empty type of free names changes. -/
def closedOperand {P : FlatInstitution.Signature.{u, u+1} κ} :
    {n : Nat} → {β : BoundCtx (Ty κ) n} → {t : Tm Empty P.Instr n} → {A : Ty κ} →
      Derivation P.Instr (Ctx.nil : Ctx Empty (Ty κ)) β t A →
        Models.Carrier (signature P).Instr Γ₀ ⟨n, β, A⟩
  | _, _, _, _, .fv (x := x) _ => x.elim
  | _, _, _, _, .bv => ⟨_, .bv⟩
  | _, _, _, _, .op a => ⟨_, .op (closedOperand a).2⟩
  | _, _, _, _, .let₁ a b => ⟨_, .let₁ (closedOperand a).2 (closedOperand b).2⟩
  | _, _, _, _, .unit => ⟨_, .unit⟩
  | _, _, _, _, .pair a b => ⟨_, .pair (closedOperand a).2 (closedOperand b).2⟩
  | _, _, _, _, .let₂ a b => ⟨_, .let₂ (closedOperand a).2 (closedOperand b).2⟩
  | _, _, _, _, .inl a => ⟨_, .inl (closedOperand a).2⟩
  | _, _, _, _, .inr a => ⟨_, .inr (closedOperand a).2⟩
  | _, _, _, _, .case e l r => ⟨_, .case (closedOperand e).2 (closedOperand l).2 (closedOperand r).2⟩
  | _, _, _, _, .abort a => ⟨_, .abort (closedOperand a).2⟩

/-- Each exact sort denotes a weak tree in a typed bound environment. -/
abbrev Arrow (Events : Type u → Type u) (i : TypingIndex (Ty κ)) :=
  BoundEnv D i.bound → ModelTree Events (D i.result)

/-- The exact LetCase operations act by the native monadic clauses.
The empty named context has no free-variable operations. -/
def operation {P : FlatInstitution.Signature.{u, u+1} κ} (M : Model (κ := κ) Events P.Instr) :
    {i : TypingIndex (Ty κ)} → (o : Models.Operation (Φ := P.Instr) Γ₀ i) →
    ((j : Fin o.arity) → Arrow Events (o.argSort j)) → Arrow Events i
  | _, .fv (x := x) _, _, _ => x.down.elim
  | _, .bv i, _, env => pure (env i)
  | _, .op f, a, env => a 0 env >>= M.instructions.denote f
  | _, .let₁ _ _, a, env => a 0 env >>= fun x => a (Fin.succ 0) (env.snoc x)
  | _, .unit, _, _ => pure PUnit.unit
  | _, .pair _ _, a, env => do
      let x ← a 0 env
      let y ← a (Fin.succ 0) env
      pure (x, y)
  | _, .let₂ _ _ _, a, env => a 0 env >>= fun xy => a (Fin.succ 0) ((env.snoc xy.1).snoc xy.2)
  | _, .inl _ _, a, env => a 0 env >>= fun x => pure (.inl x)
  | _, .inr _ _, a, env => a 0 env >>= fun x => pure (.inr x)
  | _, .case _ _ _, a, env => a 0 env >>= Sum.elim
      (fun x => a (Fin.succ 0) (env.snoc x))
      (fun y => a (Fin.succ (Fin.succ 0)) (env.snoc y))
  | _, .abort _, a, env => a 0 env >>= PEmpty.elim

/-- An actual model of the existing exact LetCase institution. -/
def algebra {P : FlatInstitution.Signature.{u, u+1} κ} (M : Model (κ := κ) Events P.Instr) :
    Algebra.{u+1, u+1, u+1}
      (Models.signature (signature P).Instr Γ₀) where
  Carrier := Arrow Events
  op := operation (P := P) M

end Silmaril.Isotope.Institution.LetCase.WeakITree
