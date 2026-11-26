module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Step

import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Thms

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasTypeEffect)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs

variable {Q K S B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "Events" => Event (Φ := Ops) carriers
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def nativeStep (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    {b : Tm Empty Ops 1} (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (state : S.Large) : ITree.Tree Events (B.Large ⊕ S.Large) :=
  db.denote D (instructions carriers P) γ (BoundEnv.snoc ρ₀ state)

private theorem raised_unfold (M : Table Q K S B) (s : S.Value) :
    M.raised.run (S.raise s) = ITree.vis (.call (Opcode.ask : Ops) (M.request s))
      (fun r => Sum.elim (fun out => ITree.ret (B.raise out))
        (fun next => M.raised.run (S.raise next)) (M.reply s r)) := by
  rw [M.raised.run_unfold]
  simp only [Table.raised, Equiv.symm_apply_apply]
  apply congrArg (ITree.vis (A := B.Large) (Event.call (Opcode.ask : Ops) (M.request s)))
  funext r
  cases M.reply s r <;> rfl

private theorem run_observe (M : Table Q K S B) :
    ∀ n s, (M.raised.run (S.raise s)).observe n = mapResult B.raise n ((M.run s).observe n) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      rw [raised_unfold M s, M.run_unfold s]
      change Part.some (ITree.Visible.vis _ _) = mapResult B.raise (n + 1) (Part.some (ITree.Visible.vis _ _))
      rw [mapResult, Part.map_some]
      dsimp only
      apply congrArg Part.some
      apply congrArg (ITree.Visible.vis (A := B.Large) (Event.call (Opcode.ask : Ops) (M.request s)))
      funext r
      cases M.reply s r with
      | inl out => cases n <;> rfl
      | inr next => exact ih next

theorem loop_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (M : Table Q K S B)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (s : S.Value)
    {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty) : (Derivation.iter da db).denote D (instructions carriers P) γ ρ₀ = M.raised.run (S.raise s) := by
  obtain ⟨t, dt, ht, hv⟩ := literal_denote P S s (β := .nil) ρ₀
  have same := Option.some.inj (ht.symm.trans ha)
  subst t
  have init := (sound carriers P (.refl da.toHasType) da dt ρ₀).trans hv
  erw [Derivation.denote, init, pure_bind]
  unfold Machine.run
  congr 1
  funext state
  change (nativeStep P db state >>= pure) = M.raised.step state
  rw [bind_pure]
  obtain ⟨v, rfl⟩ := S.raise.surjective state
  rw [nativeStep, step_denote P visible M v hf hb db]
  simp only [Machine.step, Table.raised, Equiv.symm_apply_apply]
  apply congrArg (ITree.vis (A := B.Large ⊕ S.Large) (Event.call (Opcode.ask : Ops) (M.request v)))
  funext r
  cases M.reply v r <;> rfl

theorem loop_observe (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (M : Table Q K S B)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (s : S.Value)
    {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (n : Nat) :
    ((Derivation.iter da db).denote D (instructions carriers P) γ ρ₀).observe n =
      mapResult B.raise n ((M.run s).observe n) := by
  rw [loop_denote P visible M hf s ha hb da db]
  exact run_observe M n s

theorem loop_typed (M : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b) :
    HasTypeEffect Free .nil (.iter a b) B.ty e := by
  obtain ⟨_, ia, ta⟩ := (S.literal_wf (Q := Q) (K := K) (e := e) s []).toLetIter
  obtain ⟨_, ib, tb⟩ := (M.step_wf hf).toLetIter
  exact .iter he (Option.some.inj (ia.symm.trans ha) ▸ ta) (Option.some.inj (ib.symm.trans hb) ▸ tb)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs
