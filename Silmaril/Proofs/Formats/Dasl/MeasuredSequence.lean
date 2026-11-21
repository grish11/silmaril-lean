module

public import Silmaril.Formats.Dasl.MeasuredSequence.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.MeasuredSequence

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.MeasuredSequence

variable {Name Item : Type} {item : Encode.TotalCodec Item (Shallow Name)}

theorem decodeBranch {resolve : Name → Option (Editable Item)} {leftShape rightShape : Shallow Name}
    {left right : Editable Item} (leftHit : decodeShape? item resolve leftShape = some left)
    (rightHit : decodeShape? item resolve rightShape = some right) :
    decodeShape? item resolve (branchShape leftShape rightShape) = join? left right := by
  simp [branchShape, decodeShape?, leftHit, rightHit]

theorem shapeRecovery (item : Encode.TotalCodec Item (Shallow Name))
    (resolve : Name → Option (Editable Item)) (tree : Editable Item) :
    decodeShape? item resolve (encodeShape item tree.val) = some tree := by
  obtain ⟨tree, valid⟩ := tree
  induction tree with
  | empty => rfl
  | one value => simp [encodeShape, decodeShape?, item.recovers]
  | branch length left right ihLeft ihRight =>
    obtain ⟨leftValid, rightValid, leftPos, rightPos, lengthEq⟩ := valid
    rw [encodeShape, decodeBranch (ihLeft leftValid) (ihRight rightValid)]
    simp [join?, leftPos, rightPos, lengthEq]

private theorem mapOfDecoded
    (exactItem : ∀ ⦃shape value⦄, item.decode? shape = some value → item.encode value = shape)
    {shapes : List (Shallow Name)} {items : List Item} (hit : shapes.mapM item.decode? = some items) :
    items.map item.encode = shapes := by
  induction shapes generalizing items with
  | nil => simpa using congrArg (Option.map (List.map item.encode)) hit.symm
  | cons head tail ih =>
    cases headHit : item.decode? head with
    | none => simp [List.mapM_cons, headHit] at hit
    | some value =>
      cases tailHit : tail.mapM item.decode? with
      | none => simp [List.mapM_cons, headHit, tailHit] at hit
      | some rest =>
        have same : value :: rest = items := by simpa [List.mapM_cons, headHit, tailHit] using hit
        subst items
        simp [exactItem headHit, ih tailHit]

private theorem castList {count count' : Nat} (same : count = count') (children : Fin count' → Shallow Name) :
    Tree.list count (fun index => children (Fin.cast same index)) = Tree.list count' children := by
  subst count
  rfl

private theorem encodeOfFn {count : Nat} (children : Fin count → Shallow Name) :
    Encode.list.encode (List.ofFn children) = .list count children := by
  change Tree.list (List.ofFn children).length (List.ofFn children).get = Tree.list count children
  rw [show (List.ofFn children).get = fun index => children (Fin.cast List.length_ofFn index) from
    funext (List.get_ofFn children)]
  exact castList List.length_ofFn children

theorem normalizedExact
    (exactItem : ∀ ⦃shape value⦄, item.decode? shape = some value → item.encode value = shape)
    {shape : Shallow Name} {tree : Normalized Item} (hit : (normalizedCodec item).decode? shape = some tree) :
    (normalizedCodec item).encode tree = shape := by
  change ((Encode.list.decode? shape).bind (fun values => values.mapM item.decode?)).bind
    (some ∘ Semantics.MeasuredSequence.normalEquiv.symm.toFun) = some tree at hit
  obtain ⟨items, itemsHit, rebuildHit⟩ := Option.bind_eq_some_iff.mp hit
  have rebuilt : Semantics.MeasuredSequence.normalEquiv.symm items = tree := Option.some.inj rebuildHit
  subst tree
  change Encode.list.encode
    ((Semantics.MeasuredSequence.normalEquiv (Semantics.MeasuredSequence.normalEquiv.symm items)).map item.encode) = shape
  rw [Equiv.apply_symm_apply]
  obtain ⟨values, valuesHit, decoded⟩ := Option.bind_eq_some_iff.mp itemsHit
  rw [mapOfDecoded exactItem decoded]
  cases shape <;> cases valuesHit
  exact encodeOfFn _

end Silmaril.Proofs.Formats.Dasl.MeasuredSequence
