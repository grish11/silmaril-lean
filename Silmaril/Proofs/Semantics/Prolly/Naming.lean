module

public import Silmaril.Semantics.Prolly.Defs

public section

namespace Silmaril.Proofs.Semantics.Prolly

open Silmaril.Semantics.Prolly

variable {Key Payload Name Item Output : Type}

private theorem mapM_of_eq (compute : Item → Option Output) (emit : Item → Output) (items : List Item)
    (success : ∀ item ∈ items, compute item = some (emit item)) :
    items.mapM compute = some (items.map emit) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp [success head (List.mem_cons_self ..), ih (fun item hit => success item (List.mem_cons_of_mem _ hit))]

private theorem mapM_success (compute : Item → Option Output) (emit : Item → Output)
    (items : List Item) (result : List Output) (success : items.mapM compute = some result)
    (agrees : ∀ item ∈ items, ∀ output, compute item = some output → output = emit item) :
    result = items.map emit ∧ ∀ item ∈ items, compute item = some (emit item) := by
  induction items generalizing result with
  | nil => exact ⟨(Option.some.inj success).symm, by simp⟩
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at success
    obtain ⟨headOutput, headOk, tailOutput, tailOk, rfl⟩ := success
    have headEq := agrees head (List.mem_cons_self ..) headOutput headOk
    obtain ⟨tailEq, tailAll⟩ := ih tailOutput tailOk
      (fun item hit => agrees item (List.mem_cons_of_mem _ hit))
    subst headOutput
    subst tailOutput
    exact ⟨rfl, fun item hit => (List.mem_cons.mp hit).elim (· ▸ headOk) (tailAll item)⟩

theorem nameNode_of_admits (nameBlock? : Block Name Key Payload → Option Name)
    (address : Block Name Key Payload → Name) (level : Nat) (node : Node Key Payload level)
    (admitted : (Tree.mk level node).Admits nameBlock? address) :
    nameNode? nameBlock? level node = some (address (nodeBlock address level node)) := by
  induction level with
  | zero => exact admitted _ (by simp [blockOccurrences, nodeBlock])
  | succ level ih =>
    have rootOk := admitted _ (List.mem_cons_self ..)
    have childOk : ∀ child ∈ node, nameNode? nameBlock? level child.2 =
        some (address (nodeBlock address level child.2)) := fun child hit =>
      ih child.2 (fun block occurs => admitted block (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, hit, occurs⟩)))
    simp only [nameNode?]
    rw [mapM_of_eq _ (fun child => (child.1, address (nodeBlock address level child.2))) node
      (fun child hit => by rw [childOk child hit]; rfl)]
    exact rootOk

private theorem admits_of_nameNode (nameBlock? : Block Name Key Payload → Option Name)
    (address : Block Name Key Payload → Name)
    (agrees : ∀ block name, nameBlock? block = some name → name = address block)
    (level : Nat) (node : Node Key Payload level) (name : Name)
    (success : nameNode? nameBlock? level node = some name) :
    (Tree.mk level node).Admits nameBlock? address ∧ name = address (nodeBlock address level node) := by
  induction level generalizing name with
  | zero =>
    have nameEq := agrees (.leaf node) name success
    exact ⟨by simpa [Tree.Admits, blockOccurrences, nodeBlock, nameNode?, ← nameEq] using success, nameEq⟩
  | succ level ih =>
    simp only [nameNode?, bind, Option.bind_eq_some_iff] at success
    obtain ⟨children, checked, rootOk⟩ := success
    obtain ⟨childrenEq, childOk⟩ := mapM_success _
      (fun child => (child.1, address (nodeBlock address level child.2))) node children checked (by
        intro child hit output computed
        obtain ⟨childName, named, rfl⟩ := Option.map_eq_some_iff.mp computed
        rw [(ih child.2 childName named).2])
    subst children
    have nameEq := agrees _ name rootOk
    refine ⟨?_, nameEq⟩
    intro block hit
    rcases List.mem_cons.mp hit with rfl | below
    · exact nameEq ▸ rootOk
    · obtain ⟨child, inNode, occurs⟩ := List.mem_flatMap.mp below
      obtain ⟨childName, named, _⟩ := Option.map_eq_some_iff.mp (childOk child inNode)
      exact (ih child.2 childName named).1 block occurs

theorem replayAddress_spec (tree : Tree Key Payload) (nameBlock? : Block Name Key Payload → Option Name)
    (root offDomain : Name) (hit : tree.rootName? nameBlock? = some root) :
    tree.Admits nameBlock? (replayAddress nameBlock? offDomain) ∧
      tree.rootName (replayAddress nameBlock? offDomain) = root := by
  have agrees : ∀ block name, nameBlock? block = some name → name = replayAddress nameBlock? offDomain block := by
    intro block name named
    simp [replayAddress, named]
  obtain ⟨ok, eq⟩ := admits_of_nameNode nameBlock? _ agrees tree.level tree.root root hit
  exact ⟨ok, eq.symm⟩

theorem rootName_spec (tree : Tree Key Payload) (nameBlock? : Block Name Key Payload → Option Name)
    (root : Name) : tree.rootName? nameBlock? = some root ↔
      ∃ address, tree.Admits nameBlock? address ∧ tree.rootName address = root := by
  refine ⟨fun hit => ⟨_, replayAddress_spec tree nameBlock? root root hit⟩, ?_⟩
  rintro ⟨address, ok, rfl⟩
  exact nameNode_of_admits nameBlock? address tree.level tree.root ok

end Silmaril.Proofs.Semantics.Prolly
