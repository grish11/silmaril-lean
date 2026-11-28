module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Signature.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Morphism (SignatureMap)
open Morphism.CaseSSA (erase_mapInstr)
open Institution (InstrSig)
open Institution.Acyclic
open Reverse

set_option backward.isDefEq.respectTransparency false

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]
  {d k n : Nat} {β : BoundCtx τ d} {R : Fin k → τ} {A : τ} {L : LCtx τ}

omit [TypeFormers τ] [TypeFormers υ] [g.PreservesProducts] [g.PreservesSums] in
private theorem Target.mapTypes_locals (t : Target R L A) :
    (t.mapTypes g.ty).locals = t.locals := by cases t <;> rfl

omit [TypeFormers τ] [TypeFormers υ] [g.PreservesProducts] [g.PreservesSums] in
private theorem Target.mapTypes_index (t : Target R L A) :
    (t.mapTypes g.ty).index = t.index := by cases t <;> rfl

private theorem Block.mapSignature_locals (b : Block P.Instr β R L A) :
    (b.mapSignature g).locals = b.locals := by
  cases b <;> simp [Block.mapSignature, Block.locals, Target.mapTypes_locals]

theorem table_mapSignature_localTargets (p : Table P.Instr β L n) :
    (p.mapSignature g).localTargets = p.localTargets :=
  funext fun i => (p.block i).mapSignature_locals g

private theorem Block.toSSA_mapSignature (b : Block P.Instr β R L A) :
    (b.mapSignature g).toSSA = b.toSSA.mapInstr g.instr := by
  cases b <;> simp [Block.mapSignature, Block.toSSA, Operand.mapSignature, Operand.castResult,
    Region.mapInstr, LambdaSSA.Tm.mapInstr, erase_mapInstr, Target.mapTypes_index]

theorem native_mapSignature (p : Table P.Instr β L n) (i : Fin (n + 1))
    (a : Operand P.Instr β (p.types i)) :
    (p.mapSignature g).toSSA i (a.mapSignature g) = (p.toSSA i a).mapInstr g.instr := by
  simp only [Table.toSSA, Table.entry, Table.mapSignature, Region.mapInstr, Operand.mapSignature,
    erase_mapInstr, Block.toSSA_mapSignature]

omit [TypeFormers τ] in
private theorem Target.mapTypes_id (t : Target R L A) :
    HEq (t.mapTypes id) t := by
  have eL := List.map_id L
  cases t <;> simp only [Target.mapTypes] <;> congr! (config := .unfoldSameFun) 1

omit [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums] in
private theorem Target.mapTypes_comp (t : Target R L A) :
    HEq (t.mapTypes (h.ty ∘ g.ty)) ((t.mapTypes g.ty).mapTypes h.ty) := by
  have eL : L.map (h.ty ∘ g.ty) = (L.map g.ty).map h.ty := List.map_map.symm
  cases t <;> simp only [Target.mapTypes] <;> congr! (config := .unfoldSameFun) 1

private theorem Block.mapSignature_id (b : Block P.Instr β R L A) :
    HEq (b.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) b := by
  cases b with
  | jump a t =>
    have ea := operandSignature_id_heq a
    have et := Target.mapTypes_id t
    simp only [Block.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
  | case a l r =>
    have ea := operandSignature_id_heq a
    have el := Target.mapTypes_id l
    have er := Target.mapTypes_id r
    simp only [Block.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]

private theorem Block.mapSignature_comp (b : Block P.Instr β R L A) :
    HEq (b.mapSignature (h.comp g)) ((b.mapSignature g).mapSignature h) := by
  cases b with
  | jump a t =>
    have ea := operandSignature_comp_heq g h a
    have et := Target.mapTypes_comp g h t
    simp only [Block.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]
  | @case B D a l r =>
    have ea := operandSignature_comp_cast_heq g h a
      (SignatureMap.PreservesSums.coprod (g := g) B D)
      (SignatureMap.PreservesSums.coprod (g := h) (g.ty B) (g.ty D))
      (SignatureMap.PreservesSums.coprod (g := h.comp g) B D)
    have el := Target.mapTypes_comp g h l
    have er := Target.mapTypes_comp g h r
    simp only [Block.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]

theorem table_mapSignature_id (p : Table P.Instr β L n) :
    HEq (p.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) p := by
  cases p with
  | mk types block =>
    have eβ : β.mapTypes id = β := by simp
    have eL : L.map id = L := List.map_id L
    have e : HEq (fun i => (block i).mapSignature
        (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) block := by
      apply Function.hfunext rfl
      intro i j hij
      cases eq_of_heq hij
      exact (block i).mapSignature_id
    simp only [Table.mapSignature]
    congr! (config := .unfoldSameFun) 1

theorem table_mapSignature_comp (p : Table P.Instr β L n) :
    HEq (p.mapSignature (h.comp g)) ((p.mapSignature g).mapSignature h) := by
  cases p with
  | mk types block =>
    have eβ : β.mapTypes (h.comp g).ty = (β.mapTypes g.ty).mapTypes h.ty := by
      simp [SignatureMap.comp, BoundCtx.mapTypes_comp]
    have e : HEq (fun i => (block i).mapSignature (h.comp g))
        (fun i => ((block i).mapSignature g).mapSignature h) := by
      apply Function.hfunext rfl
      intro i j hij
      cases eq_of_heq hij
      exact (block i).mapSignature_comp g h
    simp only [Table.mapSignature]
    congr! (config := .unfoldSameFun) 1
    simp [SignatureMap.comp, List.map_map]

private theorem mappedCheck (p : Table P.Instr β L n) (ok : p.check = true) :
    (p.mapSignature g).check = true := by
  unfold Table.check at *
  rw [table_mapSignature_localTargets g p]
  exact ok

private theorem blockTree_map (b : Block P.Instr β R L A)
    (next : LocalTrees (Φ := P.Instr) (β := β) (L := L) R b.locals)
    (next' : LocalTrees (Φ := Q.Instr) (β := β.mapTypes g.ty) (L := L.map g.ty)
      (g.ty ∘ R) (b.mapSignature g).locals)
    (ih : ∀ j (edge : j ∈ (b.mapSignature g).locals),
      next' j edge = (next j (b.mapSignature_locals g ▸ edge)).mapSignature g) :
    blockTree (b.mapSignature g) next' = (blockTree b next).mapSignature g := by
  cases b with
  | jump a t =>
    cases t <;> simp only [Block.mapSignature, blockTree, Target.mapTypes, targetTree,
      Tree.mapSignature, Edge.mapSignature, ih]
  | case a l r =>
    cases l <;> cases r <;> simp only [Block.mapSignature, blockTree, Target.mapTypes, targetTree,
      Tree.mapSignature, Edge.mapSignature, ih]

private theorem tableTree_map (p : Table P.Instr β L n) (ok : p.check = true) (i : Fin (n + 1)) :
    tableTree (p.mapSignature g) (mappedCheck g p ok) i = (tableTree p ok i).mapSignature g := by
  rw [tableTree.eq_def, tableTree.eq_def]
  apply blockTree_map
  intro j edge
  exact tableTree_map p ok j
termination_by p.rank i
decreasing_by
  apply p.decreases ok
  change j ∈ (p.block i).locals
  exact (p.block i).mapSignature_locals g ▸ edge

theorem tableProgram_map (p : Table P.Instr β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand P.Instr β (p.types i)) (ok' : (p.mapSignature g).check = true) :
    tableProgram (p.mapSignature g) ok' i (a.mapSignature g) = (tableProgram p ok i a).mapSignature g := by
  simp only [tableProgram, Program.mapSignature, Table.mapSignature]
  exact congrArg (fun t => Program.mk (g.ty (p.types i)) (a.mapSignature g) t) (tableTree_map g p ok i)

mutual

private theorem tree_id : ∀ {A : τ} (t : Tree P.Instr β L A),
    HEq (t.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) t
  | _, .jump a k => by
    have ea := operandSignature_id_heq a
    have ek := edge_id k
    simp only [Tree.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
  | _, .case a l r => by
    have ea := operandSignature_id_heq a
    have el := edge_id l
    have er := edge_id r
    simp only [Tree.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
termination_by structural _ t => t

private theorem edge_id : ∀ {A : τ} (k : Edge P.Instr β L A),
    HEq (k.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) k
  | _, .exit hi => by
    simp only [Edge.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
  | _, .local t => by
    have et := tree_id t
    simp only [Edge.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]
termination_by structural _ k => k

end

theorem program_mapSignature_id (p : Program P.Instr β L) :
    HEq (p.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) p := by
  cases p with
  | mk A a t =>
    have ea := operandSignature_id_heq a
    have et := tree_id t
    simp only [Program.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]

mutual

private theorem tree_comp : ∀ {A : τ} (t : Tree P.Instr β L A),
    HEq (t.mapSignature (h.comp g)) ((t.mapSignature g).mapSignature h)
  | _, .jump a k => by
    have ea := operandSignature_comp_heq g h a
    have ek := edge_comp k
    simp only [Tree.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]
  | _, .case (B := B) (D := D) a l r => by
    have ea := operandSignature_comp_cast_heq g h a
      (SignatureMap.PreservesSums.coprod (g := g) B D)
      (SignatureMap.PreservesSums.coprod (g := h) (g.ty B) (g.ty D))
      (SignatureMap.PreservesSums.coprod (g := h.comp g) B D)
    have el := edge_comp l
    have er := edge_comp r
    simp only [Tree.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]
termination_by structural _ t => t

private theorem edge_comp : ∀ {A : τ} (k : Edge P.Instr β L A),
    HEq (k.mapSignature (h.comp g)) ((k.mapSignature g).mapSignature h)
  | _, .exit hi => by
    simp only [Edge.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]
  | _, .local t => by
    have et := tree_comp t
    simp only [Edge.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]
termination_by structural _ k => k

end

theorem program_mapSignature_comp (p : Program P.Instr β L) :
    HEq (p.mapSignature (h.comp g)) ((p.mapSignature g).mapSignature h) := by
  cases p with
  | mk A a t =>
    have ea := operandSignature_comp_heq g h a
    have et := tree_comp g h t
    simp only [Program.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
