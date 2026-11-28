module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Defs
public import Silmaril.SSA.Isotope.LetCase.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Thms

/-! # Exact LetCase with typed ordered traces -/

@[expose] public section

namespace Silmaril.Isotope.LetCase.Structural.Reply

open LocallyNameless (Derivation Tm)
open Silmaril.Isotope.Semantics (BoundEnv)
open LetSeq.StraightLine.Structural (Trace Log model)
open LetIter.Semantics.Categorical (denoteOfType)
open scoped LetSeq.StraightLine.Structural

local notation "Value" => LetSeq.StraightLine.Structural.Value

variable {α Φ : Type} [HasTy Φ (Ty α)]

abbrev Γ₀ : Ctx Empty (Ty α) := .nil
abbrev Term := Tm Empty Φ

/-- Reuse the typed event model over the native signature, now allowing sums. -/
def run {n : Nat} {β : BoundCtx (Ty α) n} {t : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Value β) : Trace α Φ (Value A) :=
  d.denote Value model (fun x => x.elim) ρ

/-- Replace the newest slot, keeping every ambient slot under the new
payload binder. The two reply specializations use the native injections. -/
def specialize {n : Nat} (body value : Tm Empty Φ (n + 1)) : Tm Empty Φ (n + 1) :=
  body.bsubst (Fin.cases value (fun i => .bv i.succ))

/-- At a fixed input, a successful execution log cannot be a proper prefix
of another successful log, and determines the returned value. -/
def PrefixDetermined {A : Type} (m : Trace α Φ A) : Prop :=
  ∀ {x y u v}, (x, u) ∈ m.outcomes → (y, v) ∈ m.outcomes →
    u.toList <+: v.toList → x = y ∧ u = v

/-- The exact arms have the same observations on every reachable tagged
payload, with the original ambient environment still in scope. -/
def RepliesAgree {n : Nat} {β : BoundCtx (Ty α) n} {A B D : Ty α}
    {scr : Tm Empty Φ n} {l l' r r' : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dl' : Derivation Φ Γ₀ (β.snoc A) l' D)
    (dr : Derivation Φ Γ₀ (β.snoc B) r D) (dr' : Derivation Φ Γ₀ (β.snoc B) r' D)
    (ρ : BoundEnv Value β) : Prop :=
  (∀ a w, (Sum.inl a, w) ∈ (run d ρ).outcomes → run dl (ρ.snoc a) = run dl' (ρ.snoc a)) ∧
  (∀ b w, (Sum.inr b, w) ∈ (run d ρ).outcomes → run dr (ρ.snoc b) = run dr' (ρ.snoc b))

/-- The actual categorical denotation in the ordered trace Kleisli model. -/
noncomputable def traceArrow {n : Nat} {β : BoundCtx (Ty α) n} {t : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) :=
  denoteOfType Value (model (Φ := Φ)) (Morphism.CaseIter.derivation d)

/-- Arrow equality in the coherent central-unit shared-tensor class used in
the native LetSeq categorical comparison. -/
abbrev Valid {n : Nat} {β : BoundCtx (Ty α) n} {t u : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) : Prop :=
  LetIter.Semantics.Categorical.Syntactic.RepairedLocallySmallValidity false
    (Morphism.CaseIter.derivation d) (Morphism.CaseIter.derivation e)

namespace EmptyBoundary

abbrev signature := LetIter.Semantics.Categorical.AbortCounterexample.signature
abbrev input : BoundCtx (Ty Empty) 1 := .snoc .nil .unit

/-- The known effectful-empty counterexample, at a native unit input. -/
def scrutinee : Derivation signature.Instr Γ₀ input (.op true .unit) .empty := .op .unit

def direct : Derivation signature.Instr Γ₀ input (.abort (.op true .unit)) .unit := .abort scrutinee

def sequenced :
    Derivation signature.Instr Γ₀ input (.let₁ (.op true .unit) (.abort (.bv 0))) .unit :=
  .let₁ scrutinee (.abort .bv)

end EmptyBoundary

end Silmaril.Isotope.LetCase.Structural.Reply
