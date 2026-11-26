module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Square

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation)
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Proofs

variable {n : Nat} {F : Family n} {S B : Code} {ε : Type} [HasEff (Opcode F) ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem row_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (e : ε) (row : Row F S B) :
    ∃ (b : Tm Empty Ops 0) (db : Derivation Ops Free .nil b (Code.sum B S).ty),
      row.source.toLetIter 0 = some b ∧ db.denote D (instructions carriers P) γ ρ₀ = row.step := by
  cases row with
  | ret value => exact literal_denote P (Code.sum B S) (.inl value) ρ₀
  | call f x k =>
    obtain ⟨a, da, ha, daEq⟩ := literal_denote P f.argCode x (β := .nil) ρ₀
    obtain ⟨b, hb, tb⟩ := (reply_wf (Γ := []) (e := e) k).toLetIter
    obtain ⟨db⟩ := Derivation.ofHasType tb.1
    change (replySource k).toLetIter 1 = some b at hb
    refine ⟨.let₁ (.op f a) b, .let₁ (.op da) db, ?_, ?_⟩
    · simp [Row.source, Expr.toLetIter, ha, hb]
    · rw [denote_letOp_of_not_pure carriers P (visible f) da db ρ₀, daEq, pure_bind]
      have small : toSmall carriers (instrSrc f) (f.argCode.raise x) = x :=
        (toSmall carriers f.argCode.ty).apply_symm_apply _
      rw [small, Row.step]
      congr 1
      funext r
      obtain ⟨val, dv, lv, hv⟩ := literal_denote P (Code.sum B S) (k r) (β := .nil) ρ₀
      refine (specialize_denote P r db dv hb lv (reply_readback k r (e := e))).trans (hv.trans ?_)
      cases k r <;> rfl

theorem step_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (M : Table F S B)
    (hf : ∀ f : Ops, instrEff f ≤ e) (s : S.Value)
    {b : Tm Empty Ops 1} (hb : M.source.toLetIter 1 = some b)
    (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty) :
    db.denote D (instructions carriers P) γ (BoundEnv.snoc ρ₀ (S.raise s)) = (M s).step := by
  obtain ⟨t, dt, ht, eq⟩ := row_denote (e := e) P visible (M s)
  exact (specialize_denote P s db dt hb ht (step_readback M s hf)).trans eq

theorem loop_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (M : Table F S B)
    (hf : ∀ f : Ops, instrEff f ≤ e) (s : S.Value)
    {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty) :
    (da.iter db).denote D (instructions carriers P) γ ρ₀ = M.run s := by
  obtain ⟨t, dt, ht, hv⟩ := literal_denote P S s (β := .nil) ρ₀
  have same := Option.some.inj (ht.symm.trans ha)
  subst t
  have init := (sound carriers P (.refl da.toHasType) da dt ρ₀).trans hv
  erw [Derivation.denote, init, pure_bind]
  unfold Table.run
  congr 1
  funext state
  obtain ⟨v, rfl⟩ := S.raise.surjective state
  change (db.denote D (instructions carriers P) γ (BoundEnv.snoc ρ₀ (S.raise v)) >>= pure) =
    M.step (S.raise v)
  rw [bind_pure, step_denote P visible M hf v hb db, Table.step, Equiv.symm_apply_apply]

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Proofs
