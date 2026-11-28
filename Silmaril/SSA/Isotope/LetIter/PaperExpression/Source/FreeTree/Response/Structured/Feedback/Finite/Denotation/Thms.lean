module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Step
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Run
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Packed

/-! # Denotation and replay for rendered finite request tables -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasTypeEffect)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic (repairedDenoteInSyntax)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

section ConstructorSemantics

variable {Ops : Type} [HasTy Ops (Ty Unit)] {ε : Type} [HasEff Ops ε]
  [SemilatticeSup ε] [OrderBot ε] {e : ε}

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "Den" => Ty.denote (Lifted carriers)
local notation "Events" => Event (Φ := Ops) carriers
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem literal_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers) (c : Code) (v : c.Value)
    {n : Nat} {β : BoundCtx (Ty Unit) n} (ρ : BoundEnv Den β) :
    ∃ (t : Tm Empty Ops n) (d : Derivation Ops Free β t c.ty),
      (c.literal v).toLetIter n = some t ∧ d.denote Den (instructions carriers P) γ ρ = pure (c.raise v) :=
  DenotationProofs.literal_denote P c v ρ

variable [EffectIteration ε] in
theorem specialize_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    {c : Code} (v : c.Value) {a rhs : Expr Ops} {A : Ty Unit}
    {t : Tm Empty Ops 1} {r : Tm Empty Ops 0}
    (d : Derivation Ops Free (.snoc .nil c.ty) t A) (dr : Derivation Ops Free .nil r A)
    (hl : a.toLetIter 1 = some t) (hr : rhs.toLetIter 0 = some r)
    (eq : Source.Eqv ([] : EffectCtx (Ty Unit) ε) A e (a.subst (c.literal v).subst0) rhs) :
    d.denote Den (instructions carriers P) γ (BoundEnv.snoc ρ₀ (c.raise v)) =
      dr.denote Den (instructions carriers P) γ ρ₀ :=
  DenotationProofs.specialize_denote P v d dr hl hr eq

end ConstructorSemantics

variable {Q K S T B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε} {L : Table Q K S B} {R : Table Q K T B}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

/-- At an encoded state, the rendered body makes exactly the table request.
Every reply returns the specified encoded control result. -/
theorem step_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops))
    (M : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    {t : Tm Empty Ops 1} (hl : M.source.toLetIter 1 = some t)
    (d : Derivation Ops Free (.snoc .nil S.ty) t (Code.sum B S).ty) :
    d.denote D (instructions carriers P) γ (BoundEnv.snoc ρ₀ (S.raise s)) =
      ITree.vis (.call (Opcode.ask : Ops) (M.request s)) (fun r => ITree.ret ((Code.sum B S).raise (M.reply s r))) :=
  DenotationProofs.step_denote P visible M s hf hl d

/-- The rendered native loop denotes the full weak tree of the table
interpreter with encoded state and result types. -/
theorem loop_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (M : Table Q K S B)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (s : S.Value)
    {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty) :
    (Derivation.iter da db).denote D (instructions carriers P) γ ρ₀ = M.raised.run (S.raise s) :=
  DenotationProofs.loop_denote P visible M hf s ha hb da db

/-- At every depth, the native weak tree agrees with the original table
after changing only the encoding of result values. -/
theorem loop_observe (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (M : Table Q K S B)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (s : S.Value)
    {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (n : Nat) :
    ((Derivation.iter da db).denote D (instructions carriers P) γ ρ₀).observe n =
      mapResult B.raise n ((M.run s).observe n) :=
  DenotationProofs.loop_observe P visible M hf s ha hb da db n

/-- The rendered loop is typed at the supplied iterative bound. -/
theorem loop_typed (M : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b) :
    HasTypeEffect Free .nil (.iter a b) B.ty e :=
  DenotationProofs.loop_typed M s hf he ha hb

/-- Equality of the actual native weak denotations is equivalent to equality
of the original table trees. -/
theorem native_denote_eq_iff {s : S.Value} {t : T.Value} {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    (Derivation.iter da db).denote (Ty.denote (Lifted carriers)) (instructions carriers P)
        (fun x => x.elim) (fun i => i.elim0) =
      (Derivation.iter da' db').denote (Ty.denote (Lifted carriers)) (instructions carriers P)
        (fun x => x.elim) (fun i => i.elim0) ↔
      L.run s = R.run t :=
  DenotationProofs.native_denote_eq_iff ha hb ha' hb' da db da' db' P visible hf

/-- Equality in the repaired packed model implies table observation equality. -/
theorem run_eq_of_packed_eq {s : S.Value} {t : T.Value} {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (packed : repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da db) =
      repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da' db')) :
    L.run s = R.run t :=
  DenotationProofs.run_eq_of_packed_eq ha hb ha' hb' da db da' db' P visible hf packed

/-- When all left states are reachable and right requests distinguish states,
table observation equality replays as repaired packed equality. -/
theorem packed_eq_iff {s : S.Value} {t : T.Value} {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) (separates : Function.Injective R.request) (reach : ∀ x, L.Reaches s x) :
    repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da db) = repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da' db') ↔
      L.run s = R.run t :=
  DenotationProofs.packed_eq_iff ha hb ha' hb' da db da' db' P visible hf he separates reach

/-- Replay equality of the actual weak denotations as equality in the
repaired packed model under the table recovery hypotheses. -/
theorem packed_eq_iff_native_denote_eq {s : S.Value} {t : T.Value} {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) (separates : Function.Injective R.request) (reach : ∀ x, L.Reaches s x) :
    repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da db) = repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da' db') ↔
      (Derivation.iter da db).denote (Ty.denote (Lifted carriers)) (instructions carriers P)
        (fun x => x.elim) (fun i => i.elim0) =
      (Derivation.iter da' db').denote (Ty.denote (Lifted carriers)) (instructions carriers P)
        (fun x => x.elim) (fun i => i.elim0) :=
  (packed_eq_iff ha hb ha' hb' da db da' db' P visible hf he separates reach).trans
    (native_denote_eq_iff ha hb ha' hb' da db da' db' P visible hf).symm

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
