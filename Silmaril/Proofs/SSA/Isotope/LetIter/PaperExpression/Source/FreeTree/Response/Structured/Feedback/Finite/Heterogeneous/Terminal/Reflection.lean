module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Thms
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Normalize

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
  (repairedDenoteInSyntax repairedDenoteInSyntax_eq_iff)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

variable {n : Nat} {F : Family n} {S T B : Code}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

theorem contract_guarded (M : Table F S B) : Guarded M.contract := by
  intro s t f x k row r next
  cases hs : M s with
  | ret v => simp [Table.contract, hs] at row
  | call g y j =>
    simp only [Table.contract, hs] at row
    cases row
    cases hj : j r with
    | inl v => simp [hj, Table.contractReply] at next
    | inr w =>
      cases hw : M w with
      | ret v => simp [hj, Table.contractReply, hw] at next
      | call g y j' =>
        have eq : w = t := Sum.inr.inj (by simpa only [hj, Table.contractReply, hw] using next)
        subst t
        exact ⟨g, y, fun reply => M.contractReply (j' reply), by simp [Table.contract, hw]⟩

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

local notation "E" => AbortEquiv (Φ := Ops) (⊥ : ε) Free

private theorem typed_loop (M : Table F S B) (s : S.Value) (hf : ∀ f : Ops, instrEff f ≤ e)
    (he : IsIterative e) :
    HasTypeEffect Free .nil (.iter (nativeValue Ops S s) (nativeBody M)) B.ty e := by
  have init : Wf ([] : EffectCtx (Ty Unit) ε) (S.literal s : Expr Ops) S.ty e :=
    Finite.literal_wf S s
  obtain ⟨a, la, ta⟩ := init.toLetIter
  obtain ⟨b, lb, tb⟩ := (M.step_wf hf).toLetIter
  have sameA := Option.some.inj (la.symm.trans (value_lowers S s 0))
  have sameB := Option.some.inj (lb.symm.trans (body_lowers M))
  exact .iter he (sameA ▸ ta) (sameB ▸ tb)

theorem contract_eq (M : Table F S B) (s : S.Value) (hf : ∀ f : Ops, instrEff f ≤ e)
    (he : IsIterative e) {a : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (hb' : M.contract.source.toLetIter 1 = some b') :
    HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a b') B.ty e ∧
      E .nil (.iter a b) (.iter a b') B.ty := by
  have sameA := Option.some.inj (ha.symm.trans (value_lowers S s 0))
  have sameB := Option.some.inj (hb.symm.trans (body_lowers M))
  have sameB' := Option.some.inj (hb'.symm.trans (body_lowers M.contract))
  subst a b b'
  exact ⟨typed_loop M s hf he, typed_loop M.contract s hf he, contract_native M s⟩

theorem contract_run (M : Table F S B) (s : S.Value) (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (hf : ∀ f : Ops, instrEff f ≤ e) :
    M.run s = M.contract.run s := by
  obtain ⟨da⟩ := Derivation.ofHasType (value_typed S s (Φ := Ops) .nil)
  obtain ⟨db⟩ := Derivation.ofHasType (body_typed M)
  obtain ⟨db'⟩ := Derivation.ofHasType (body_typed M.contract)
  have weak := sound carriers P (contract_native (pe := (⊥ : ε)) M s) (da.iter db) (da.iter db') ρ₀
  rw [loop_denote P visible M hf s (value_lowers S s 0) (body_lowers M) da db,
    loop_denote P visible M.contract hf s (value_lowers S s 0) (body_lowers M.contract) da db'] at weak
  exact weak

variable {L : Table F S B} {R : Table F T B} {s : S.Value} {t : T.Value}

theorem replay_full (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f)
    (obs : L.run s = R.run t) (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s).toLetIter 0 = some a ∧ (T.literal t).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      E .nil (.iter a b) (.iter a' b') B.ty := by
  have after := (contract_run L s P visible hf).symm.trans (obs.trans (contract_run R t P visible hf))
  have aligned : ReplyAligned L.contract R.contract s t :=
    aligned_of_guarded after (contract_guarded L) (contract_guarded R)
  obtain ⟨al, ar, bl, br, ha, ha', hb, hb', _, _, bridge⟩ := replay_of_run_eq (s := s) (t := t) after aligned hf he
  have sa := Option.some.inj (ha.symm.trans (value_lowers S s 0))
  have sa' := Option.some.inj (ha'.symm.trans (value_lowers T t 0))
  have sb := Option.some.inj (hb.symm.trans (body_lowers L.contract))
  have sb' := Option.some.inj (hb'.symm.trans (body_lowers R.contract))
  subst al ar bl br
  exact ⟨_, _, _, _, value_lowers S s 0, value_lowers T t 0, body_lowers L, body_lowers R,
    typed_loop L s hf he, typed_loop R t hf he, (contract_native L s).trans
      (bridge.trans (contract_native R t).symm)⟩

theorem packed_eq_iff_full {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      L.run s = R.run t := by
  constructor
  · intro packed
    have native := (repairedDenoteInSyntax_eq_iff (⊥ : ε) (da.iter db) (da'.iter db')).mp packed
    have weak := sound carriers P native (da.iter db) (da'.iter db') ρ₀
    rw [loop_denote P visible L hf s ha hb da db, loop_denote P visible R hf t ha' hb' da' db'] at weak
    exact weak
  · intro obs
    obtain ⟨a₀, a₁, b₀, b₁, ha₀, ha₁, hb₀, hb₁, _, _, native⟩ := replay_full (s := s) (t := t) P visible obs hf he
    have ea := Option.some.inj (ha₀.symm.trans ha)
    have ea' := Option.some.inj (ha₁.symm.trans ha')
    have eb := Option.some.inj (hb₀.symm.trans hb)
    have eb' := Option.some.inj (hb₁.symm.trans hb')
    subst a₀ a₁ b₀ b₁
    exact (repairedDenoteInSyntax_eq_iff (⊥ : ε) (da.iter db) (da'.iter db')).mpr native

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
