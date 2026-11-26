module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Run
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Encoding

import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Thms

public section

open Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
  (repairedDenoteInSyntax repairedDenoteInSyntax_eq_iff)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs

variable {Q K S T B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε} {L : Table Q K S B} {R : Table Q K T B}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

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
      L.run s = R.run t := by
  refine ⟨fun weak => ?_, fun obs => ?_⟩
  · apply ITree.Tree.ext
    intro n
    have eq := (loop_observe P visible L hf s ha hb da db n).symm.trans
      ((congrArg (fun u => ITree.Tree.observe u n) weak).trans (loop_observe P visible R hf t ha' hb' da' db' n))
    have reflect := congrArg (mapResult B.raise.symm n) eq
    rw [mapResult_leftInverse (f := B.raise) (g := B.raise.symm) B.raise.left_inv,
      mapResult_leftInverse (f := B.raise) (g := B.raise.symm) B.raise.left_inv] at reflect
    exact reflect
  · apply ITree.Tree.ext
    intro n
    rw [loop_observe P visible L hf s ha hb da db n, loop_observe P visible R hf t ha' hb' da' db' n, obs]

theorem run_eq_of_packed_eq {s : S.Value} {t : T.Value} {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (packed : repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da db) =
      repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da' db')) :
    L.run s = R.run t := by
  have native := (repairedDenoteInSyntax_eq_iff (⊥ : ε) (Derivation.iter da db) (Derivation.iter da' db')).mp packed
  exact (native_denote_eq_iff ha hb ha' hb' da db da' db' P visible hf).mp
    (sound carriers P native (Derivation.iter da db) (Derivation.iter da' db') (fun i => i.elim0))

theorem packed_eq_iff {s : S.Value} {t : T.Value} {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops)) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    (he : IsIterative e) (separates : Function.Injective R.request) (reach : ∀ x, L.Reaches s x) :
    repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da db) = repairedDenoteInSyntax (⊥ : ε) (Derivation.iter da' db') ↔
      L.run s = R.run t := by
  refine ⟨run_eq_of_packed_eq ha hb ha' hb' da db da' db' P visible hf, fun obs => ?_⟩
  obtain ⟨a₀, a₁, b₀, b₁, ha₀, ha₁, hb₀, hb₁, _, _, native⟩ := replay separates reach obs hf he
  have ea := Option.some.inj (ha₀.symm.trans ha)
  subst a₀
  have ea' := Option.some.inj (ha₁.symm.trans ha')
  subst a₁
  have eb := Option.some.inj (hb₀.symm.trans hb)
  subst b₀
  have eb' := Option.some.inj (hb₁.symm.trans hb')
  subst b₁
  exact (repairedDenoteInSyntax_eq_iff (⊥ : ε) (Derivation.iter da db) (Derivation.iter da' db')).mpr native

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs
