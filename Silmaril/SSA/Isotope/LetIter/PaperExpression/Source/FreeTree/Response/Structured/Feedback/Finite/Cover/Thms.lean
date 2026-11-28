module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Cover.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Cover.Construct
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Cover.Replay

/-! # Reflection by synchronized finite feedback tables -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasTypeEffect AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic (repairedDenoteInSyntax)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

variable {Q K S T B : Code} {L : Table Q K S B} {R : Table Q K T B} {s : S.Value} {t : T.Value}

/-- Initial observation equality propagates along each shared repeat path. -/
theorem PairedReach.run_eq (obs : L.run s = R.run t)
    {p : S.Value × T.Value} (reach : PairedReach L R s t p) :
    L.run p.1 = R.run p.2 :=
  CoverProofs.run_eq_of_reach obs reach

/-- Equal initial observations give a table on the reachable pairs. Each
projection preserves requests, return values, and repeat successors. -/
theorem exists_cover (obs : L.run s = R.run t) : Nonempty (Cover L R s t) :=
  CoverProofs.exists_cover obs

variable {ε : Type} [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Render the common cover and replay both projection maps by native pure
uniformity. Both original tables are typed at the supplied bound. -/
theorem replay_of_run_eq (obs : L.run s = R.run t)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s).toLetIter 0 = some a ∧ (T.literal t).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty :=
  CoverProofs.replay_of_run_eq obs hf he

/-- Actual repaired packed equality is equivalent to original table observation
equality for the visible one-request renderer. -/
theorem packed_eq_iff_run_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      L.run s = R.run t :=
  CoverProofs.packed_eq_iff_run_eq ha hb ha' hb' da db da' db' P visible hf he

/-- Actual equality of the native weak denotations replays as repaired packed
equality for the rendered tables. -/
theorem packed_eq_iff_rendered_denote_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da db) = repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da' db') ↔
      (Derivation.iter da db).denote (Ty.denote (Lifted carriers)) (instructions carriers P)
        (fun x => x.elim) (fun i => i.elim0) =
      (Derivation.iter da' db').denote (Ty.denote (Lifted carriers)) (instructions carriers P)
        (fun x => x.elim) (fun i => i.elim0) :=
  (packed_eq_iff_run_eq ha hb ha' hb' da db da' db' P visible hf he).trans
    (native_denote_eq_iff ha hb ha' hb' da db da' db' P visible hf).symm

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
