module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs
public import Silmaril.Languages.Python.Compile.Closure.Body.Thms
public import Silmaril.Languages.Python.Core.Closure.Dispatch.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closure.Link

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure
open Compile.Closure.Link
open Core.Closure (CodeRef Layout)
open Core.Closure.Dispatch (Definition Entry resolve resolve_iff)

private def HasTarget (first : Nat) (blocks : List Block) (ref : Source.BlockPath × CodeRef) : Prop :=
  ∃ (offset : Nat) (block : Block),
    ref.2.key = first + offset ∧ blocks[offset]? = some block ∧
      block.path = ref.1 ∧ block.entry.layout = ref.2.layout

private theorem HasTarget.before {first : Nat} {left : List Block} (right : List Block)
    {ref : Source.BlockPath × CodeRef}
    (found : HasTarget first left ref) : HasTarget first (left ++ right) ref := by
  obtain ⟨offset, block, key, entry, path, layout⟩ := found
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp entry
  exact ⟨offset, block, key, (List.getElem?_append_left bound).trans entry, path, layout⟩

private theorem HasTarget.after {first : Nat} (left : List Block) {right : List Block}
    {ref : Source.BlockPath × CodeRef}
    (found : HasTarget (first + left.length) right ref) : HasTarget first (left ++ right) ref := by
  obtain ⟨offset, block, key, entry, path, layout⟩ := found
  refine ⟨left.length + offset, block, by omega, ?_, path, layout⟩
  simpa [List.getElem?_append_right (Nat.le_add_right left.length offset)] using entry

private theorem HasTarget.cons {first : Nat} (block : Block) {rest : List Block}
    {ref : Source.BlockPath × CodeRef}
    (found : HasTarget (first + 1) rest ref) : HasTarget first (block :: rest) ref := by
  obtain ⟨offset, target, key, entry, path, layout⟩ := found
  exact ⟨offset + 1, target, by omega, entry, path, layout⟩

private def blockReferences (blocks : List Block) : List (Source.BlockPath × CodeRef) :=
  blocks.flatMap (fun block => block.entry.definition.body.references)

private theorem link_targets {layout : Layout} (tree : Source.ScopeTree) (first : Nat)
    (code : Body.Code layout) :
    let lowered := linkBody first tree code
    (∀ ref ∈ lowered.code.references, HasTarget first lowered.children ref) ∧
      (∀ ref ∈ blockReferences lowered.children, HasTarget first lowered.children ref) := by
  induction code generalizing first with
  | ret => simp [linkBody, Code.references, blockReferences]
  | assign _ _ _ tail | assert _ _ tail | assertFreeVars _ _ _ _ tail
  | assertCellVars _ _ _ tail | assertCodeNames _ _ _ tail | discardCall _ _ tail =>
    simpa [linkBody, Code.references] using tail first
  | closure slot path childLayout parameters captures child rest inner tail =>
    let nested := linkBody (first + 1) tree child
    let later := linkBody (first + 1 + nested.children.length) tree rest
    let entry : Entry Code := ⟨childLayout, { parameters, body := nested.code }⟩
    let newBlock := ((Block.mk path entry).withFreeVars tree).withCellVars tree
    have nestedTargets := inner (first + 1)
    have laterTargets := tail (first + 1 + nested.children.length)
    have hasNested {ref : Source.BlockPath × CodeRef} (target : HasTarget (first + 1) nested.children ref) :
        HasTarget first (newBlock :: (nested.children ++ later.children)) ref :=
      (target.before later.children).cons newBlock
    have hasLater {ref : Source.BlockPath × CodeRef}
        (target : HasTarget (first + 1 + nested.children.length) later.children ref) :
        HasTarget first (newBlock :: (nested.children ++ later.children)) ref :=
      (target.after nested.children).cons newBlock
    constructor
    · intro ref member
      change ref ∈ (path, ⟨first, childLayout⟩) :: later.code.references at member
      rcases List.mem_cons.mp member with rfl | laterMember
      · exact ⟨0, newBlock, (Nat.add_zero _).symm, rfl, rfl, rfl⟩
      · exact hasLater (laterTargets.1 ref laterMember)
    · intro ref member
      change ref ∈ blockReferences (newBlock :: (nested.children ++ later.children)) at member
      rw [blockReferences, List.flatMap_cons, List.flatMap_append, List.mem_append, List.mem_append] at member
      rcases member with own | innerBlock | laterBlock
      · exact hasNested (nestedTargets.1 ref own)
      · exact hasNested (nestedTargets.2 ref innerBlock)
      · exact hasLater (laterTargets.2 ref laterBlock)

private theorem link_paths {layout : Layout} (tree : Source.ScopeTree) (first : Nat)
    (code : Body.Code layout) :
    (linkBody first tree code).children.map Block.path = code.childPaths := by
  induction code generalizing first with
  | ret => rfl
  | assign _ _ _ tail | assert _ _ tail | assertFreeVars _ _ _ _ tail
  | assertCellVars _ _ _ tail | assertCodeNames _ _ _ tail | discardCall _ _ tail =>
    simpa [linkBody, Body.Code.childPaths] using tail first
  | closure _ _ _ _ _ _ _ inner tail =>
    simp [linkBody, Block.withFreeVars, Block.withCellVars, Body.Code.childPaths, inner, tail]

theorem paths {source : Source.Module} (compiled : Body.Compiled source) :
    (link compiled).blocks.map Block.path = compiled.paths := by
  simp [link, Block.withFreeVars, Block.withCellVars, Body.Compiled.paths, link_paths]

theorem resolve_reference {source : Source.Module} (compiled : Body.Compiled source)
    {path : Source.BlockPath} {ref : CodeRef} (emitted : (path, ref) ∈ (link compiled).references) :
    ∃ definition : Definition Code ref.layout,
      (link compiled).blocks[ref.key]? = some ⟨path, ⟨ref.layout, definition⟩⟩ ∧
      resolve (link compiled).table ref = .ok definition := by
  let body := linkBody 1 compiled.moduleTree compiled.code
  let layout := Compile.Closure.frameLayout compiled.tree.scope
  let entry : Entry Code := ⟨layout, { parameters := compiled.parameters, body := body.code }⟩
  let root := ((Block.mk compiled.tree.scope.context.path entry).withFreeVars compiled.moduleTree)
    |>.withCellVars compiled.moduleTree
  have rootOrChild : (path, ref) ∈ body.code.references ∨ (path, ref) ∈ blockReferences body.children := by
    simpa [Program.references, link, body, Block.withFreeVars, Block.withCellVars, blockReferences] using emitted
  have targets := link_targets compiled.moduleTree 1 compiled.code
  have found : HasTarget 1 body.children (path, ref) :=
    rootOrChild.elim (targets.1 (path, ref)) (targets.2 (path, ref))
  obtain ⟨offset, ⟨actualPath, actualLayout, definition⟩, key, entry, pathMatch, same⟩ :=
    found.cons (first := 0) root
  change actualLayout = ref.layout at same
  refine ⟨same ▸ definition, ?_, resolve_iff.mpr ?_⟩
  · change (root :: body.children)[ref.key]? = _
    change actualPath = path at pathMatch
    rw [show ref.key = offset by simpa using key, entry, pathMatch]
    cases same
    rfl
  · change ((root :: body.children)[ref.key]?).map Block.entry = _
    rw [show ref.key = offset by simpa using key, entry]
    cases same
    rfl

end Silmaril.Proofs.Languages.Python.Compile.Closure.Link
