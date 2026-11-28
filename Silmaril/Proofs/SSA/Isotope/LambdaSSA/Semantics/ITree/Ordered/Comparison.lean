module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Signature.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered

open CategoryTheory
open scoped Silmaril.Elgot.ITree.WeakKleisli
open Silmaril.Elgot.ITree (Tree TraceLE)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (denoteArrow denoteArrow_ofRegion)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Morphism (SignatureMap)
open Silmaril.Isotope.Semantics (encodeValue encodeValue_injective)

universe u v w

variable {κ : Type (u + 1)} [AtomValues κ] {Events : Type u → Type u}
  {Φ : Type v} {Ψ : Type w} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  [HasTy Ψ (Ty κ)] [HasEff Ψ Bool] {A B : Ty κ}

attribute [local instance] typeModel categoricalInstructions

local notation "V" => AtomValues.carrier (κ := κ)
local notation "Interp" => Ty.denote V
local notation "TM" => ModelTree Events
local notation "K" => typeJ (m := TM)
local notation "T" => Silmaril.Isotope.LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

private theorem denote_tree (M : Model (κ := κ) Events Φ) (p : Program Φ A B)
    (x : Interp A) (env : Env (Sigma V)) :
    ((show TM (Interp B) from (p.denote M).of x) >>=
      fun b => pure (0, encodeValue V B b)) =
    region M.raw (extend env (encodeValue V A x)) p.code := by
  let _ := M.instructions
  exact singletonDenote_tree M.raw M.compatible p.typed x env

theorem denote_le_iff (M : Model (κ := κ) Events Φ) (N : Model (κ := κ) Events Ψ)
    (p : Program Φ A B) (q : Program Ψ A B) (env : Env (Sigma V)) :
    p.denote M ≤ q.denote N ↔ ∀ x : Interp A,
      TraceLE.{u, u+1} (region M.raw (extend env (encodeValue V A x)) p.code)
        (region N.raw (extend env (encodeValue V A x)) q.code) := by
  have injective : Function.Injective (fun b => (0, encodeValue V B b)) :=
    fun _ _ eq => encodeValue_injective V B (congrArg Prod.snd eq)
  apply forall_congr'
  intro x
  rw [← denote_tree M p x env, ← denote_tree N q x env]
  exact (TraceLE.bind_pure_iff injective).symm

theorem denote_ofCFG (M : Model (κ := κ) Events Φ)
    {blocks exits : Nat} {R : Fin blocks → Ty κ} {D : Fin exits → Ty κ}
    {g : FiniteCFG Φ blocks exits 0} (hg : g.HasType .nil R D) :
    (Program.ofCFG hg).denote M =
      (let _ := M.instructions; denoteArrow K T (FiniteCFG.packedExecution hg)) := by
  let _ := M.instructions
  let _ := regionTypingCoherent M.raw M.compatible
  rw [FiniteCFG.packedExecution_ofRegion, denoteArrow_ofRegion K T (fun _ _ => ⟨rfl, rfl⟩)]
  rfl

theorem satisfies_ofCFG_iff (M : Model (κ := κ) Events Φ)
    {blocks blocks' exits : Nat} {R : Fin blocks → Ty κ} {R' : Fin blocks' → Ty κ}
    {D : Fin exits → Ty κ} {g : FiniteCFG Φ blocks exits 0} {h : FiniteCFG Φ blocks' exits 0}
    (hg : g.HasType .nil R D) (hh : h.HasType .nil R' D) (env : Env (Sigma V)) :
    M.Satisfies (Program.ofCFG hg) (Program.ofCFG hh) ↔
      TraceLE.{u, u+1} (region M.raw env (FiniteCFG.packedExecutionRegion hg))
        (region M.raw env (FiniteCFG.packedExecutionRegion hh)) := by
  rw [Model.Satisfies, denote_le_iff M M (Program.ofCFG hg) (Program.ofCFG hh) env]
  simp only [Program.ofCFG, FiniteCFG.packedExecution_representative_tree,
    FiniteCFG.packedExecution_tree]
  exact ⟨fun h => h PUnit.unit, fun h _ => h⟩

private theorem encode_cast (h : A = B) (x : Interp A) :
    encodeValue V B (cast (congrArg Interp h) x) = encodeValue V A x := by
  cases h
  rfl

private theorem bind_encode_cast (h : A = B) (t : ModelTree Events (Interp A)) :
    (cast (congrArg (fun sort => ModelTree Events (Interp sort)) h) t >>=
      fun y => pure (encodeValue V B y)) = (t >>= fun y => pure (encodeValue V A y)) := by
  cases h
  rfl

theorem reduct_compatible (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    (bottom : g.eff ⊥ = ⊥) :
    Compatible (κ' := κ) ⟨(M.reductInstructions g types bottom).denote⟩
      (fun f => M.raw (g.instr f)) := by
  intro f x
  let source : (instrSrc (g.instr f) : Ty κ) = instrSrc f :=
    (g.source f).trans (congrFun types _)
  let target : (instrTrg (g.instr f) : Ty κ) = instrTrg f :=
    (g.target f).trans (congrFun types _)
  let input := cast (congrArg Interp source.symm) x
  let call := M.instructions.denote (g.instr f) input
  change M.raw (g.instr f) (encodeValue V _ x) =
    (cast (congrArg (fun sort => ModelTree Events (Interp sort)) target) call >>= fun y =>
      pure (encodeValue V _ y))
  rw [bind_encode_cast target, ← encode_cast source.symm x]
  exact M.compatible (g.instr f) input

theorem denote_reduct (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    (p : Program Φ A B) (N : Model (κ := κ) Events Φ)
    (raw : N.raw = fun f => M.raw (g.instr f)) :
    p.denote N = (p.map g types).denote M := by
  let env : Env (Sigma V) := fun _ => .unit
  have erased (x : Interp A) :
      region M.raw (extend env (encodeValue V A x)) (p.map g types).code =
        region N.raw (extend env (encodeValue V A x)) p.code := by
    rw [raw]
    exact region_mapInstr g.instr M.raw _ p.code
  apply le_antisymm
  · exact (denote_le_iff _ _ _ _ env).mpr fun x => (erased x) ▸ TraceLE.refl _
  · exact (denote_le_iff _ _ _ _ env).mpr fun x => (erased x).symm ▸ TraceLE.refl _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered
