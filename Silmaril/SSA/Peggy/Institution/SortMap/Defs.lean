module

public import Silmaril.SSA.Peggy.Institution.Thms
public import Silmaril.SSA.PEG.SortMap.Thms

/-! # Peggy signatures with variable data sorts -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SortMap

open CategoryTheory
open Dialect (FixedSortSignature OpenGraph)

universe u v w

/-- The data sorts are part of the signature. The PEG control and count
sorts are still built into the core. -/
structure Signature where
  Data : Type u
  ops : PEG.InstructionSet.{u,v} Data

structure Hom (S T : Signature.{u,v}) where
  sorts : S.Data → T.Data
  opcode : PEG.ProfileMap sorts S.ops T.ops

variable {S T U : Signature.{u,v}}

def Signature.ofFixed {D : Type u} (S : FixedSortSignature.{u,v} D) : Signature.{u,v} :=
  ⟨D, S.ops⟩

abbrev Signature.fixed (S : Signature.{u,v}) : FixedSortSignature.{u,v} S.Data := ⟨S.ops⟩

def Hom.ofFixed {D : Type u} {S T : FixedSortSignature.{u,v} D} (op : S ⟶ T) :
    Hom (Signature.ofFixed S) (Signature.ofFixed T) :=
  ⟨_root_.id, PEG.ProfileMap.fixed (P := S.ops) (Q := T.ops) (FixedSortSignature.opcodeMap op)⟩

def Hom.id (S : Signature.{u,v}) : Hom S S :=
  ⟨_root_.id, PEG.ProfileMap.fixed (P := S.ops) (Q := S.ops) (fun op => op)⟩

def Hom.comp (f : Hom S T) (g : Hom T U) : Hom S U :=
  ⟨g.sorts ∘ f.sorts, PEG.ProfileMap.comp f.opcode g.opcode⟩

abbrev Model (S : Signature.{u,v}) := Institution.Model.{u,v,w} S.fixed

/-- Use the canonical open equation type over each signature's own sorts. -/
abbrev Equation (S : Signature.{u,v}) := Dialect.Equation S.fixed

def reduct (f : Hom S T) (m : Model.{u,v,w} T) : Model.{u,v,w} S :=
  m.reductData f.opcode

def mapOpenGraph (f : Hom S T) {params results : List (PEG.Ty S.Data)} {nodes loops : Nat}
    {forest : PEG.LoopForest loops} (graph : OpenGraph S.ops params results nodes forest) :
    OpenGraph T.ops (PEG.Ty.mapProfile f.sorts params) (PEG.Ty.mapProfile f.sorts results) nodes forest :=
  ⟨graph.graph.mapData f.opcode, graph.forest_eq, (graph.graph.wellFormed_mapData f.opcode).mpr graph.wellFormed⟩

def Equation.map (f : Hom S T) (e : Equation S) : Equation T where
  params := PEG.Ty.mapProfile f.sorts e.params
  results := PEG.Ty.mapProfile f.sorts e.results
  loops := e.loops
  forest := e.forest
  leftNodes := e.leftNodes
  rightNodes := e.rightNodes
  lhs := mapOpenGraph f e.lhs
  rhs := mapOpenGraph f e.rhs

end Silmaril.SSA.Peggy.SortMap
