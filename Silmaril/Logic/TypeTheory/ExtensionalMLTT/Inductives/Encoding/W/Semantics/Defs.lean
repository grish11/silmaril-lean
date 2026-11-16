module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Terms.Thms

@[expose] public section

/-! Native raw trees and their exact set-valued root, coherence witnesses and indexed fibres. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

noncomputable section
open Classical

/-- The actual native W-type whose code set interprets the original raw carrier. -/
abbrev Description.NativeRaw (S : Description) (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) :=
  WSet.Tree (S.totalShape.denoteIn U ρ Fin.elim0)
    (fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0))

/-- The original source index stored in the root's tagged set label. -/
def Description.nativeRoot (S : Description) (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) :
    S.NativeRaw U ρ → ZFSet.{u}
  | .mk a _ => SetSem.fst a.val

/-- Interpret the original child-index term under the exact index/shape/position values. -/
def Description.nativeNext (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (a p : ZFSet.{u}) : ZFSet.{u} :=
  S.next.denoteIn U ρ (Fin.cons p (Fin.cons (SetSem.snd a) (Fin.cons (SetSem.fst a) Fin.elim0)))

/-- Every recursive edge and every descendant has its original requested source index. -/
def Description.nativeCoherent (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) : S.NativeRaw U ρ → Prop
  | .mk a f => ∀ b, S.nativeRoot U ρ (f b) = S.nativeNext U ρ a.val b.val ∧
      S.nativeCoherent U ρ (f b)

/-- The actual graph-valued dependent product of edge equality and recursive witnesses. -/
def Description.nativeCoherenceType (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) : S.NativeRaw U ρ → ZFSet.{u}
  | .mk a f => SetSem.pi (S.positions.denoteIn U ρ (Fin.cons a.val Fin.elim0)) fun p =>
      if hp : p ∈ S.positions.denoteIn U ρ (Fin.cons a.val Fin.elim0) then
        SetSem.sigma (SetSem.truth (S.nativeRoot U ρ (f ⟨p, hp⟩) = S.nativeNext U ρ a.val p))
          (fun _ => S.nativeCoherenceType U ρ (f ⟨p, hp⟩))
      else ∅

/-- The canonical witness graph; membership is proved precisely for coherent trees. -/
def Description.nativeCoherenceWitness (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) : S.NativeRaw U ρ → ZFSet.{u}
  | .mk _ f => WSet.graph fun p => SetSem.pair ∅ (S.nativeCoherenceWitness U ρ (f p))

/-- Native raw trees with the original root index and recursive edge invariant. -/
def Description.NativeFibre (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (i : ZFSet.{u}) :=
  {t : S.NativeRaw U ρ // S.nativeRoot U ρ t = i ∧ S.nativeCoherent U ρ t}

/-- Code an original fibre including its actual nested equality and coherence witnesses. -/
def Description.nativeFibreCode (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) {i : ZFSet.{u}} (t : S.NativeFibre U ρ i) : ZFSet.{u} :=
  SetSem.pair (WSet.encode (A := S.totalShape.denoteIn U ρ Fin.elim0)
    (B := fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0)) t.val)
    (SetSem.pair ∅ (S.nativeCoherenceWitness U ρ t.val))

/-- Restrict a supplied infinite hierarchy to the laws needed at one finite stage. -/
def hierarchyFiniteModel (T : SetHierarchy.{u}) (levels : ℕ) :
    Silmaril.Logic.SetTheory.FiniteTower.{u} levels where
  U := T.U
  isGrothendieck i _ := T.isGrothendieck i
  mem_succ i _ := T.mem_succ i

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
