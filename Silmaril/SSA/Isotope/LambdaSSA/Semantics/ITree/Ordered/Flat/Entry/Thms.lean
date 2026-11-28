module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Entry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.InstructionMap.Thms

/-! # Syntactic and semantic squares for a supplied entry record -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered

open Silmaril.Isotope.Morphism (SignatureMap)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree (TraceLE)
open LambdaSSA.Semantics (extend)

universe u v w

variable {κ : Type (u + 1)} {Φ : Type v} {Ψ : Type w}
  [HasTy Φ (Ty κ)] [HasEff Φ Bool] [HasTy Ψ (Ty κ)] [HasEff Ψ Bool]
  {n blocks blocks' exits : Nat} {β : BoundCtx (Ty κ) n}
  {R : Fin blocks → Ty κ} {R' : Fin blocks' → Ty κ} {D : Fin exits → Ty κ}
  {g : FiniteCFG Φ blocks exits n} {h : FiniteCFG Φ blocks' exits n}

/-- The primitive map keeps the same external entry record type. -/
theorem Program.ofCFGEntry_mapInstr (f : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool)
    (types : f.ty = id) (hg : g.HasType β R D) :
    Program.ofCFGEntry (hg.mapInstr (flatProfiles f types)) = (Program.ofCFGEntry hg).map f types := by
  simp only [Program.ofCFGEntry, Program.map, Program.mk.injEq, Region.packInputsDestructure_mapInstr]
  exact congrArg (fun r => r.packInputsDestructure β.toList)
    (FiniteCFG.packedExecutionRegion_mapInstr f.instr (flatProfiles f types) hg)

variable [AtomValues κ] {Events : Type u → Type u}

local notation "V" => AtomValues.carrier (κ := κ)
local notation "A" => Region.packedInputType β.toList

/-- Use the existing trace order at every well-typed external input. Ambient
slots can be chosen freely because the singleton programs have exact typing. -/
theorem satisfies_ofCFGEntry_iff (M : Model (κ := κ) Events Φ)
    (hg : g.HasType β R D) (hh : h.HasType β R' D) (env : Env (Sigma V)) :
    M.Satisfies (Program.ofCFGEntry hg) (Program.ofCFGEntry hh) ↔
      ∀ x : Ty.denote V A,
        TraceLE (region M.raw (extend env (encodeValue V A x)) (Program.ofCFGEntry hg).code)
          (region M.raw (extend env (encodeValue V A x)) (Program.ofCFGEntry hh).code) :=
  denote_le_iff M M (Program.ofCFGEntry hg) (Program.ofCFGEntry hh) env

/-- The existing model reduct compares the two written entry-taking tables. -/
theorem satisfies_ofCFGEntry_map_iff (M : Model (κ := κ) Events Ψ)
    (f : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : f.ty = id) (bottom : f.eff ⊥ = ⊥)
    (hg : g.HasType β R D) (hh : h.HasType β R' D) :
    M.Satisfies (Program.ofCFGEntry (hg.mapInstr (flatProfiles f types)))
      (Program.ofCFGEntry (hh.mapInstr (flatProfiles f types))) ↔
    (M.reduct f types bottom).Satisfies (Program.ofCFGEntry hg) (Program.ofCFGEntry hh) := by
  rw [Program.ofCFGEntry_mapInstr f types hg, Program.ofCFGEntry_mapInstr f types hh,
    satisfies_map_iff M]

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
