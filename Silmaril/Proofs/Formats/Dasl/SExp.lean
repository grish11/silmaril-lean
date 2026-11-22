module

public import Silmaril.Formats.Dasl.SExp.Defs
public import Silmaril.Formats.Dasl.Resolve.Refinement.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.SExp

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.SExp
open Silmaril.Formats (SExp2)
open Silmaril.Semantics.Naming

variable {Atom Name Ref Item Target : Type}

private theorem collect_some {len : Nat} (items : Fin len → Item) :
    collect (fun index => some (items index)) = some items := by
  simp [collect]

private theorem collect_mono {len : Nat} {low high : Fin len → Option Item}
    (step : ∀ index item, low index = some item → high index = some item) {items : Fin len → Item}
    (hit : collect low = some items) : collect high = some items := by
  unfold collect at hit
  split at hit
  next ready =>
    have each := Option.some.inj hit
    have hits (index : Fin len) : low index = some (items index) := by
      rw [← each]
      cases found : low index <;> simp_all
    have next := funext fun index => step index (items index) (hits index)
    rw [next, collect_some]
  next => contradiction

private theorem read_atom (payload : Payload Atom) (atom : Atom) :
    readAtomFields (Ref := Ref) (Name := Name) payload atomKeys (fun _ => .bytes (payload.encode atom)) =
      some atom := by
  simp [readAtomFields, readAtom, payload.recovers]

theorem proper_read_at_write_at (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name)
    (path : Path) (item : Formats.SExp Atom) (child : Bool) :
    Proper.readAt payload child (Proper.writeAt (Ref := Ref) payload put path item) = some item := by
  induction item generalizing path child with
  | atom value => simp [Proper.writeAt, atomNode, Proper.readAt, read_atom]
  | list len items ih =>
    rw [Proper.writeAt, Proper.readAt]
    have hits : (fun index => Proper.readAt payload true
        (edge put (index.val :: path) (items index)
          (Proper.writeAt (Ref := Ref) payload put (index.val :: path) (items index)))) =
        fun index => some (items index) := by
      funext index
      unfold edge
      split
      · exact ih index (index.val :: path) true
      · simpa only [Proper.readAt, ite_true] using ih index (index.val :: path) false
    rw [hits, collect_some]
    rfl

theorem proper_embed (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name)
    (path : Path) (item : Formats.SExp Atom) :
    Named.embed (Proper.writeAt payload put path item) = Proper.writeAt payload put path item := by
  induction item generalizing path with
  | atom => rfl
  | list len items ih =>
    rw [Proper.writeAt, Proper.writeAt]
    apply congrArg (Tree.list len)
    funext index
    change Named.embed (edge put (index.val :: path) (items index) _) = edge put (index.val :: path) (items index) _
    cases hit : put (index.val :: path) (items index) with
    | none => simpa only [edge, hit] using ih index (index.val :: path)
    | some name =>
      simp only [edge, hit, Named.embed, Tree.map]
      exact congrArg (Tree.obj name) (ih index (index.val :: path))

private theorem distinct_keys : Dotted.pairKeys ≠ atomKeys := by
  intro same
  have car : "car" ∈ Dotted.pairKeys := by simp [Dotted.pairKeys]
  simp [same, atomKeys] at car

theorem dotted_read_at_write_at (layout : Dotted.Layout) (payload : Payload Atom)
    (put : Placement (SExp2 Atom) Name) (path : Path) (item : SExp2 Atom) (child : Bool) :
    Dotted.readAt layout payload child (Dotted.writeAt (Ref := Ref) layout payload put path item) =
      some item := by
  induction item generalizing path child with
  | nil => simp [Dotted.writeAt, Dotted.readAt]
  | atom value => simp [Dotted.writeAt, atomNode, Dotted.readAt, distinct_keys.symm, read_atom]
  | cons car cdr ihCar ihCdr =>
    have placed (index : Nat) (branch : SExp2 Atom)
        (ih : ∀ (path : Path) (child : Bool), Dotted.readAt layout payload child
          (Dotted.writeAt (Ref := Ref) layout payload put path branch) = some branch) :
        Dotted.readAt layout payload true (edge put (index :: path) branch
          (Dotted.writeAt (Ref := Ref) layout payload put (index :: path) branch)) = some branch := by
      unfold edge
      split
      · exact ih _ true
      · simpa only [Dotted.readAt, ite_true] using ih (index :: path) false
    have left := placed 0 car ihCar
    have right := placed 1 cdr ihCdr
    cases layout <;> simp [Dotted.writeAt, Dotted.pair, Encode.pairEntry, Dotted.readAt, left, right]

private theorem atom_mono (payload : Payload Atom) {low high : Partial Name}
    (step : Extends low high) {value : Atom} (hit : readAtom payload low = some value) :
    readAtom payload high = some value := by
  cases step <;> exact hit

private theorem fields_mono (payload : Payload Atom) {keys : Finset String}
    {low high : ↥keys → Partial Name} (step : ∀ key, Extends (low key) (high key))
    {value : Atom} (hit : readAtomFields payload keys low = some value) :
    readAtomFields payload keys high = some value := by
  unfold readAtomFields at *
  split at hit <;> rename_i guard
  · rw [dite_eq_left guard]
    exact atom_mono payload (step _) hit
  · contradiction

theorem proper_mono (payload : Payload Atom) {low high : Partial Name} (step : Extends low high)
    (child : Bool) {item : Formats.SExp Atom} (hit : Proper.readAt payload child low = some item) :
    Proper.readAt payload child high = some item := by
  induction step generalizing child item with
  | same => exact hit
  | openObj | openBlob => cases hit
  | obj _ step ih => cases child <;> simp_all [Proper.readAt]
  | dict steps _ => exact Option.map_eq_some_iff.mpr (by
      obtain ⟨value, read, eq⟩ := Option.map_eq_some_iff.mp hit
      exact ⟨value, fields_mono payload steps read, eq⟩)
  | list _ ih => exact Option.map_eq_some_iff.mpr (by
      obtain ⟨values, read, eq⟩ := Option.map_eq_some_iff.mp hit
      exact ⟨values, collect_mono (fun index _ => ih index true) read, eq⟩)

theorem dotted_mono (layout : Dotted.Layout) (payload : Payload Atom) {low high : Partial Name}
    (step : Extends low high) (child : Bool) {item : SExp2 Atom}
    (hit : Dotted.readAt layout payload child low = some item) : Dotted.readAt layout payload child high = some item := by
  induction step generalizing child item with
  | same => exact hit
  | openObj | openBlob => cases hit
  | obj _ step ih => cases child <;> simp_all [Dotted.readAt]
  | dict steps ih =>
    rw [Dotted.readAt] at hit ⊢
    split at hit <;> rename_i guard
    · rw [dite_eq_left guard]
      obtain ⟨car, left, rest⟩ := Option.bind_eq_some_iff.mp hit
      obtain ⟨cdr, right, eq⟩ := Option.bind_eq_some_iff.mp rest
      exact Option.bind_eq_some_iff.mpr ⟨car, ih _ true left,
        Option.bind_eq_some_iff.mpr ⟨cdr, ih _ true right, eq⟩⟩
    · rw [dite_eq_right guard]
      obtain ⟨value, read, eq⟩ := Option.map_eq_some_iff.mp hit
      exact Option.map_eq_some_iff.mpr ⟨value, fields_mono payload steps read, eq⟩
  | @list len low high steps ih =>
    match len with
    | 0 | 1 | _ + 3 => cases hit
    | 2 =>
      rw [Dotted.readAt] at hit ⊢
      split at hit <;> rename_i guard
      · rw [ite_eq_left guard]
        obtain ⟨car, left, rest⟩ := Option.bind_eq_some_iff.mp hit
        obtain ⟨cdr, right, eq⟩ := Option.bind_eq_some_iff.mp rest
        exact Option.bind_eq_some_iff.mpr ⟨car, ih _ true left,
          Option.bind_eq_some_iff.mpr ⟨cdr, ih _ true right, eq⟩⟩
      · contradiction

theorem observations_agree {store : Store Name} (bound : store.Binding)
    (read : Partial Name → Option Item)
    (mono : ∀ ⦃low high item⦄, Extends low high → read low = some item → read high = some item)
    {root : Name} {tree : Named Name} (full : FullNames store root tree) {item : Item} :
    Observes store read root item ↔ read tree.embed = some item := by
  exact ⟨fun ⟨_, present, hit⟩ => mono (full.refines bound present) hit,
    fun hit => ⟨tree.embed, full.toPartial, hit⟩⟩

theorem norms_equal (codec : Encode.TotalCodec Item Target) (read : Tree Ref Name → Option Item)
    {left right : Tree Ref Name} {first second : Item} (leftHit : read left = some first)
    (rightHit : read right = some second) :
    normalize read codec.encode left = normalize read codec.encode right ↔ first = second := by
  simp only [normalize, leftHit, rightHit, Option.map_some, Option.some.injEq]
  exact ⟨fun same => Option.some.inj ((codec.recovers first).symm.trans (same ▸ codec.recovers second)),
    congrArg codec.encode⟩

theorem expands_of_bindings {store : Store Name} (tree : Named Name)
    (included : tree.embed.bindings.Subset store) : Expands store tree.embed.shallow tree := by
  induction tree with
  | ref impossible => exact impossible.elim
  | obj name target ih =>
    exact .obj (included.1 (Or.inl ⟨rfl, rfl⟩))
      (ih ⟨fun _ _ hit => included.1 (Or.inr hit), included.2⟩)
  | blob name payload => exact .blob (included.2 ⟨rfl, rfl⟩)
  | dict keys values ih | list keys values ih =>
    constructor
    intro index
    exact ih index ⟨fun _ _ hit => included.1 ⟨index, hit⟩, fun _ _ hit => included.2 ⟨index, hit⟩⟩
  | _ => constructor

theorem alias_iff_norm {store : Store Name} (bound : store.Binding)
    (read : Partial Name → Option Item) (codec : Encode.TotalCodec Item Target)
    {left right : Name} {leftTree rightTree : Named Name}
    (leftFull : FullNames store left leftTree) (rightFull : FullNames store right rightTree) :
    Aliases store read left right ↔ ∃ normal,
      normalize read codec.encode leftTree.embed = some normal ∧
      normalize read codec.encode rightTree.embed = some normal := by
  constructor
  · rintro ⟨item, ⟨first, firstFull, firstHit⟩, ⟨second, secondFull, secondHit⟩⟩
    rw [fullNames_binding bound firstFull leftFull] at firstHit
    rw [fullNames_binding bound secondFull rightFull] at secondHit
    exact ⟨codec.encode item, by simp [normalize, firstHit], by simp [normalize, secondHit]⟩
  · rintro ⟨normal, firstHit, secondHit⟩
    obtain ⟨first, readFirst, writeFirst⟩ := Option.map_eq_some_iff.mp firstHit
    obtain ⟨second, readSecond, writeSecond⟩ := Option.map_eq_some_iff.mp secondHit
    have eq : first = second := Option.some.inj
      ((codec.recovers first).symm.trans ((writeFirst.trans writeSecond.symm) ▸ codec.recovers second))
    exact ⟨first, ⟨leftTree, leftFull, readFirst⟩, ⟨rightTree, rightFull, eq.symm ▸ readSecond⟩⟩

end Silmaril.Proofs.Formats.Dasl.SExp
