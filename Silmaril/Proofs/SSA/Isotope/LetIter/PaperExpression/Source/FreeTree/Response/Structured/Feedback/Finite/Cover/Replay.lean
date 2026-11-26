module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Cover.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Cover.Construct

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasTypeEffect AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
  (repairedDenoteInSyntax repairedDenoteInSyntax_eq_iff)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.CoverProofs

variable {Q K S T B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε} {L : Table Q K S B} {R : Table Q K T B} {s : S.Value} {t : T.Value}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

theorem replay_of_run_eq (obs : L.run s = R.run t)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s).toLetIter 0 = some a ∧ (T.literal t).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty := by
  obtain ⟨C⟩ := exists_cover obs
  have start := C.decode.apply_symm_apply ⟨(s, t), PairedReach.initial⟩
  have startL : (C.decode C.initial).val.1 = s := congrArg (fun p => p.val.1) start
  have startR : (C.decode C.initial).val.2 = t := congrArg (fun p => p.val.2) start
  obtain ⟨ac, a, bc, b, hac, ha, hbc, hb, _, tyL, eqL⟩ := replay_commutes C.left_commutes startL hf he
  obtain ⟨ac', a', bc', b', hac', ha', hbc', hb', _, tyR, eqR⟩ := replay_commutes C.right_commutes startR hf he
  have ea := Option.some.inj (hac'.symm.trans hac)
  have eb := Option.some.inj (hbc'.symm.trans hbc)
  subst ac' bc'
  exact ⟨a, a', b, b', ha, ha', hb, hb', tyL, tyR, eqL.symm.trans eqR⟩

theorem packed_eq_iff_run_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      L.run s = R.run t := by
  refine ⟨run_eq_of_packed_eq ha hb ha' hb' da db da' db' P visible hf, fun obs => ?_⟩
  obtain ⟨a₀, a₁, b₀, b₁, ha₀, ha₁, hb₀, hb₁, _, _, native⟩ := replay_of_run_eq obs hf he
  have ea := Option.some.inj (ha₀.symm.trans ha)
  have ea' := Option.some.inj (ha₁.symm.trans ha')
  have eb := Option.some.inj (hb₀.symm.trans hb)
  have eb' := Option.some.inj (hb₁.symm.trans hb')
  subst a₀ a₁ b₀ b₁
  exact (repairedDenoteInSyntax_eq_iff (⊥ : ε) (da.iter db) (da'.iter db')).mpr native

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.CoverProofs
