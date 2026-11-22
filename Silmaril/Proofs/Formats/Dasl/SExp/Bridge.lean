module

public import Silmaril.Formats.Dasl.SExp.Bridge.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.SExp.Bridge

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.SExp

variable {Atom Name Ref Item Target : Type} {store : Store Name}

theorem observed_rel (bound : store.Binding) (read : Partial Name → Option Item)
    (mono : ∀ ⦃low high item⦄, Extends low high → read low = some item → read high = some item)
    (left right : FullRoot store) : (observedPER store bound read).rel left right ↔
    ∃ item, Observes store read left.val item ∧ Observes store read right.val item := by
  obtain ⟨leftTree, leftFull⟩ := left.property
  obtain ⟨rightTree, rightFull⟩ := right.property
  change Aliases store read left.val right.val ↔ _
  constructor
  · rintro ⟨item, ⟨first, firstFull, firstHit⟩, ⟨second, secondFull, secondHit⟩⟩
    rw [fullNames_binding bound firstFull leftFull] at firstHit
    rw [fullNames_binding bound secondFull rightFull] at secondHit
    exact ⟨item, (observations_agree bound read mono leftFull).2 firstHit,
      (observations_agree bound read mono rightFull).2 secondHit⟩
  · rintro ⟨item, leftHit, rightHit⟩
    exact ⟨item, ⟨leftTree, leftFull, (observations_agree bound read mono leftFull).1 leftHit⟩,
      ⟨rightTree, rightFull, (observations_agree bound read mono rightFull).1 rightHit⟩⟩

theorem presentation_rel_normalize (read : Tree Ref Name → Option Item)
    (codec : Encode.TotalCodec Item Target) (left right : Tree Ref Name) :
    (presentationPER read).rel left right ↔ ∃ normal,
      normalize read codec.encode left = some normal ∧ normalize read codec.encode right = some normal := by
  constructor
  · rintro ⟨item, leftHit, rightHit⟩
    exact ⟨codec.encode item, by simp [normalize, leftHit], by simp [normalize, rightHit]⟩
  · rintro ⟨normal, leftHit, rightHit⟩
    obtain ⟨first, hfirst, hleft⟩ := Option.map_eq_some_iff.mp leftHit
    obtain ⟨second, hsecond, hright⟩ := Option.map_eq_some_iff.mp rightHit
    exact ⟨first, hfirst, codec.injective (hright.trans hleft.symm) ▸ hsecond⟩

theorem inline_write_at (payload : Payload Atom) (item : Formats.SExp Atom) (path : Path) :
    Proper.writeAt (Ref := Empty) (Name := Unit) payload inlineAll path item =
      SExpDasl.encode payload.asValue item := by
  induction item generalizing path with
  | atom => rfl
  | list len items ih =>
    exact congrArg (Tree.list len) (funext fun index => ih index (index.val :: path))

theorem rivest_inline (item : Formats.SExp Bytes) :
    Proper.writeAt (Ref := Empty) (Name := Unit) Payload.bytes inlineAll [] (item.map Bytes.data) =
      SExpDasl.rivest.encode item := by
  rw [inline_write_at]
  induction item with
  | atom => rfl
  | list len items ih => exact congrArg (Tree.list len) (funext ih)

theorem dotted_proper_hit (layout : Dotted.Layout) (payload : Payload Atom)
    (atom : Encode.TotalCodec Atom Value) (tree : Tree Ref Name) (item : Formats.SExp Atom) :
    Dotted.properAbstract? layout payload atom tree = some ((SExpDasl.codec atom).intoAbstract item) ↔
      Dotted.read layout payload tree = some item.toSExp2 := by
  classical
  unfold Dotted.properAbstract?
  constructor
  · intro accepted
    obtain ⟨datum, hit, recovered⟩ := Option.bind_eq_some_iff.mp accepted
    split at recovered
    next valid =>
      let equiv := Formats.SExp.equivProperSubtype Atom
      have selected : equiv.symm ⟨datum, valid⟩ = item :=
        (SExpDasl.codec atom).intoAbstract_injective (Option.some.inj recovered)
      have same := congrArg Subtype.val (equiv.apply_symm_apply ⟨datum, valid⟩)
      change (equiv.symm ⟨datum, valid⟩).toSExp2 = datum at same
      exact hit.trans (congrArg some ((congrArg Formats.SExp.toSExp2 selected).symm.trans same)).symm
    next => contradiction
  · intro hit
    rw [hit, Option.bind_some, dite_eq_left (Formats.SExp.toSExp2_proper item)]
    exact congrArg (some ∘ (SExpDasl.codec atom).intoAbstract)
      ((Formats.SExp.equivProperSubtype Atom).symm_apply_apply item)

end Silmaril.Proofs.Formats.Dasl.SExp.Bridge
