module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Semantics
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Replay
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Pure
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.PureContext

/-! # Two-program comparison for checked captured ranked graphs -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)
open scoped MonoidalCategory

universe u v w x y h k

section Model

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type x} {C : Type y} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  {d n m : Nat} {β : BoundCtx τ d} {L : LCtx τ}
  (p : Table Φ β L n) (q : Table Φ β L m) (hp : p.check = true) (hq : q.check = true)
  (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Operand Φ β (p.types i)) (b : Operand Φ β (q.types j))

include shared

/-- The packed region has the actual emitted LetCase arrow with input and
singleton label conversions. The emitted term tags exits by their original positions. -/
theorem Table.packed_denote :
    denoteRegion J M (p.packedSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M (p.toLetCase hp i a).2 ≫
        J.map (labelInject M (L := [packedExitType L]) 0 rfl) :=
  packed_denote_proof J M shared p hp i a

/-- In the same model, packed original arrows agree exactly when the actual
emitted typed LetCase arrows agree. The two tables may have different sizes. -/
theorem Table.packed_denote_iff :
    denoteRegion J M (p.packedSSA_hasType i a) = denoteRegion J M (q.packedSSA_hasType j b) ↔
      LetCase.Semantics.Categorical.denote J M (p.toLetCase hp i a).2 =
        LetCase.Semantics.Categorical.denote J M (q.toLetCase hq j b).2 :=
  packed_denote_iff_proof J M shared p q hp hq i j a b

end Model

section Replay

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {d n m : Nat} {β : BoundCtx (Ty α) d} {L : LCtx (Ty α)}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

/-- Replay typed native LetCase derivations through the actual SSA reifier.
The only additional root obligation is pure let β outside constructor values. -/
theorem reify_equiv_of_pureLetBeta (beta : PureLetBetaReplay (Ψ := Φ) (α := α) pe)
    {a b : LetCase.LocallyNameless.Tm Empty Φ d} {A : Ty α}
    (da : Derivation Φ Γ₀ β a A) (db : Derivation Φ Γ₀ β b A) (eq : Equiv pe Γ₀ β a b A) :
    ReplayEqv pe β.toList ((Code.ofLetCase da).guardedSSA 0) ((Code.ofLetCase db).guardedSSA 0) [A] :=
  reify_equiv_proof beta da db eq

variable (p : Table Φ β L n) (q : Table Φ β L m) (hp : p.check = true) (hq : q.check = true)
  (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Operand Φ β (p.types i)) (b : Operand Φ β (q.types j))

/-- Both actual packed graphs compare by the same native relation on their
guarded LetCase reifications, using the two checked one-program round trips. -/
theorem Table.packed_replay_iff_reified :
    ReplayEqv pe β.toList (p.packedSSA i a) (q.packedSSA j b) [packedExitType L] ↔
      ReplayEqv pe β.toList ((Code.ofLetCase (p.toLetCase hp i a).2).guardedSSA 0)
        ((Code.ofLetCase (q.toLetCase hq j b).2).guardedSSA 0) [packedExitType L] :=
  let left := p.toLetCase_reify (pe := pe) hp i a
  let right := q.toLetCase_reify (pe := pe) hq j b
  ⟨fun eq => left.symm.trans (eq.trans right), fun eq => left.trans (eq.trans right.symm)⟩

/-- Transport a native LetCase derivation at the two emitted operands back to
the original packed graphs, given the remaining pure let β rule. -/
theorem Table.packed_replay_of_equiv (beta : PureLetBetaReplay (Ψ := Φ) (α := α) pe)
    (eq : Equiv pe Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (packedExitType L)) :
    ReplayEqv pe β.toList (p.packedSSA i a) (q.packedSSA j b) [packedExitType L] :=
  (p.packed_replay_iff_reified (pe := pe) q hp hq i j a b).mpr (reify_equiv_of_pureLetBeta beta _ _ eq)

open Region.Paper.RetainedLet (returnOnce)

/-- A case rebuilding a sum of units with literal payloads is a valid
substituend for any exactly typed continuation. -/
theorem unit_case_letBeta {k : Tm Φ} {Γ : VCtx (Ty α)} {D : Ty α}
    (h : Tm.HasType Γ (.var 0 : Tm Φ) (Ty.coprod Ty.unit Ty.unit))
    (hk : Tm.HasType (Ty.coprod Ty.unit Ty.unit :: Γ) k D) :
    ReplayEqv pe Γ (returnOnce (.let₁ (.case (.var 0) (.inl .unit) (.inr .unit)) k))
      (returnOnce (k.subst (Tm.singleSubst (.case (.var 0) (.inl .unit) (.inr .unit))))) [D] :=
  unit_case_beta_proof h hk

/-- For atom-free types, constructor specialization proves pure let β for
any continuation when the effect marking excludes pure primitive calls. -/
theorem PureLetBetaReplay.of_noPureInstructions {Ψ : Type v} [HasTy Ψ (Ty Empty)] [HasEff Ψ ε]
    (noPure : ∀ f : Ψ, ¬ IsPure pe f) : PureLetBetaReplay (α := Empty) (Ψ := Ψ) pe :=
  pureLetBetaReplay_proof noPure

end Replay

section Finite

open LetCase.Structural.Finite (StructuralContext Context Types)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d n m : Nat} {β : Context d} {L : List Types}
  (p : Table Φ β L n) (q : Table Φ β L m) (hp : p.check = true) (hq : q.check = true)
  (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Operand Φ β (p.types i)) (b : Operand Φ β (q.types j))

/-- The finite trace signature marks all primitive calls as effectful, so
every pure let β instance has a proof in the existing SSA replay closure. -/
theorem finite_pureLetBetaReplay : PureLetBetaReplay (α := Empty) (Ψ := Φ) false :=
  PureLetBetaReplay.of_noPureInstructions (fun _ hf => Bool.noConfusion hf)

/-- Native finite-signature LetCase derivations transport through the actual
guarded reifier, including pure let β on computed expressions. -/
theorem reify_equiv_finite {t u : LetCase.LocallyNameless.Tm Empty Φ d} {A : Types}
    (dt : Derivation Φ Γ₀ β t A) (du : Derivation Φ Γ₀ β u A) (eq : Equiv false Γ₀ β t u A) :
    ReplayEqv false β.toList ((Code.ofLetCase dt).guardedSSA 0) ((Code.ofLetCase du).guardedSSA 0) [A] :=
  reify_equiv_of_pureLetBeta finite_pureLetBetaReplay dt du eq

/-- Inhabited finite inputs and primitive interfaces admit the existing
ordered typed trace separator on the original packed CFGs. -/
theorem Table.packed_trace_iff_equiv (input : StructuralContext β) :
    (let := traceInstructions (α := Empty) (Φ := Φ)
     denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (p.packedSSA_hasType i a) =
       denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (q.packedSSA_hasType j b)) ↔
      Equiv false Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (packedExitType L) :=
  packed_trace_iff_proof p q hp hq i j a b input

/-- Soundness followed by the finite separator reflects a native SSA proof
back to LetCase derivability on the inhabited finite structural fragment. -/
theorem Table.equiv_of_packed_replay (input : StructuralContext β)
    (eq : ReplayEqv false β.toList (p.packedSSA i a) (q.packedSSA j b) [packedExitType L]) :
    Equiv false Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (packedExitType L) :=
  packed_replay_implies_equiv_proof p q hp hq i j a b input eq

/-- The inhabited finite structural separator and native reifier transport
give a two-sided syntactic comparison once the remaining pure let β rule is available. -/
theorem Table.packed_replay_iff_equiv (input : StructuralContext β)
    (beta : PureLetBetaReplay (Ψ := Φ) (α := Empty) false) :
    ReplayEqv false β.toList (p.packedSSA i a) (q.packedSSA j b) [packedExitType L] ↔
      Equiv false Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (packedExitType L) :=
  ⟨p.equiv_of_packed_replay q hp hq i j a b input, p.packed_replay_of_equiv q hp hq i j a b beta⟩

/-- At inhabited finite inputs, native SSA replay and native LetCase
derivability compare the original packed graphs and their actual emitted terms. -/
theorem Table.packed_replay_iff_equiv_finite (input : StructuralContext β) :
    ReplayEqv false β.toList (p.packedSSA i a) (q.packedSSA j b) [packedExitType L] ↔
      Equiv false Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (packedExitType L) :=
  p.packed_replay_iff_equiv q hp hq i j a b input finite_pureLetBetaReplay

end Finite

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
