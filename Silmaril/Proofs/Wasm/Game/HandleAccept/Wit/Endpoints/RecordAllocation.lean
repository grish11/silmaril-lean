module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordAllocation

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

variable (quirks : Quirks) (encoding : StringEncoding) (width : AddrType)

private abbrev Fits (type : TypeOf) (value : Val) := Lower.fits quirks encoding width type value = true

private theorem entriesMember {fields : List Field} {type : TypeOf} {child : Field}
    (layout : Field.EntriesMatch fields type) (member : child ∈ fields) : child.LayoutMatches type := by
  induction fields with
  | nil => simp at member
  | cons _ _ ih =>
    cases layout with
    | cons head rest =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact head
      · exact ih rest tail

private theorem valuesMember {fields : List Field} {child : Field} (member : child ∈ fields) :
    child.value ∈ Field.values fields := by
  induction fields with
  | nil => simp at member
  | cons _ _ ih =>
    simp only [Field.values, List.mem_cons]
    rcases List.mem_cons.mp member with rfl | tail
    · exact .inl rfl
    · exact .inr (ih tail)

private theorem recordChild {types : List (String × TypeOf)} {fields : List Field} {child : Field}
    (layout : Field.FieldsMatch fields (types.map Prod.snd)) (member : child ∈ fields)
    (fits : Lower.fitsFields quirks encoding width types (Field.values fields) = true) :
    ∃ type, child.LayoutMatches type ∧ Fits quirks encoding width type child.value := by
  induction types generalizing fields with
  | nil => cases layout; simp at member
  | cons head tail ih =>
    cases layout with
    | cons first rest =>
      simp only [Field.values, Lower.fitsFields, Bool.and_eq_true] at fits
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨head.2, first, fits.1⟩
      · exact ih rest later fits.2

private theorem tupleChild {types : List TypeOf} {fields : List Field} {child : Field}
    (layout : Field.FieldsMatch fields types) (member : child ∈ fields)
    (fits : Lower.fitsTypes quirks encoding width types (Field.values fields) = true) :
    ∃ type, child.LayoutMatches type ∧ Fits quirks encoding width type child.value := by
  induction types generalizing fields with
  | nil => cases layout; simp at member
  | cons _ _ ih =>
    cases layout with
    | cons first rest =>
      simp only [Field.values, Lower.fitsTypes, Bool.and_eq_true] at fits
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, first, fits.1⟩
      · exact ih rest later fits.2

private theorem caseFits {types : List (String × Option TypeOf)} {tag : Nat} {selected : Option TypeOf}
    {value : Option Val} (arm : (types.map Prod.snd)[tag]? = some selected) :
    Lower.fitsCases quirks encoding width types tag value = Lower.fitsOpt quirks encoding width selected value := by
  induction types generalizing tag with
  | nil => simp at arm
  | cons head tail ih =>
    cases tag with
    | zero =>
      have equal : head.2 = selected := by simpa using arm
      simp [Lower.fitsCases, equal]
    | succ tag => exact ih (by simpa using arm)

private theorem armChild {child : Field} {type : Option TypeOf} (layout : Field.ArmMatches (some child) type)
    (fits : Lower.fitsOpt quirks encoding width type (some child.value) = true) :
    ∃ selected, child.LayoutMatches selected ∧ Fits quirks encoding width selected child.value := by
  cases layout with
  | some checked => exact ⟨_, checked, fits⟩

private theorem mapKey {key : WIT.KeyType} {value : Val}
    (fits : (match value with
      | .string str => decide (StoreStringPre quirks encoding width str)
      | _ => true) = true) :
    Fits quirks encoding width (.prim key.toPrimitive) value := by
  cases key <;> cases value <;> simp_all [Fits, WIT.KeyType.toPrimitive, Lower.fits]

private theorem mapEntry {key : WIT.KeyType} {type : TypeOf} {entry : Val}
    (fits : (match entry with
      | .record [keyValue, value] =>
        (match keyValue with
          | .string str => decide (StoreStringPre quirks encoding width str)
          | _ => true) && Lower.fits quirks encoding width type value
      | _ => false) = true) :
    Fits quirks encoding width (.record (mapEntryFields key type)) entry := by
  cases entry <;> try contradiction
  rename_i values
  rcases values with (_ | ⟨keyValue, _ | ⟨value, _ | ⟨_, _⟩⟩⟩) <;> try contradiction
  dsimp only at fits
  simp only [Bool.and_eq_true] at fits
  obtain ⟨keyFit, valueFit⟩ := fits
  simp only [Fits, Lower.fits, Val.recordCheck, mapEntryFields, Lower.fitsFields, Bool.and_eq_true, and_true]
  exact ⟨mapKey quirks encoding width keyFit, valueFit⟩

theorem descendant {root child : Field} {type : TypeOf} (path : Field.Descendant root child)
    (layout : root.LayoutMatches type) (fits : Lower.fits quirks encoding width type root.value = true) :
    child.LayoutMatches child.type ∧ Lower.fits quirks encoding width child.type child.value = true := by
  induction path generalizing type with
  | self field => simpa only [layout.type_eq] using And.intro layout fits
  | aggregate member path ih =>
    cases layout with
    | record checked =>
      obtain ⟨_, next, admitted⟩ := recordChild quirks encoding width checked member
        (by simpa only [Fits, Field.value, Lower.fits, Val.recordCheck] using fits)
      exact ih next admitted
    | tuple checked =>
      obtain ⟨_, next, admitted⟩ := tupleChild quirks encoding width checked member
        (by simpa only [Fits, Field.value, Lower.fits, Val.recordCheck] using fits)
      exact ih next admitted
  | fixed member path ih =>
    cases layout with
    | fixed _ checked =>
      simp only [Field.value, Lower.fits, Val.listCheck, List.all_eq_true] at fits
      exact ih (entriesMember checked member) (fits _ (valuesMember member))
  | dynamic member path ih =>
    cases layout with
    | list checked =>
      simp only [Field.value, Lower.fits, Bool.and_eq_true, List.all_eq_true] at fits
      exact ih (entriesMember checked member) (fits.2 _ (valuesMember member))
    | map checked =>
      simp only [Field.value, Lower.fits, Bool.and_eq_true, List.all_eq_true] at fits
      exact ih (entriesMember checked member) (mapEntry quirks encoding width (fits.2 _ (valuesMember member)))
  | sum path ih =>
    cases layout with
    | variant selected checked =>
      simp only [Field.value, Lower.fits, Val.variantCheck, caseFits quirks encoding width selected,
        Field.armValue] at fits
      obtain ⟨_, next, admitted⟩ := armChild quirks encoding width checked fits
      exact ih next admitted
    | optionSome checked =>
      exact ih checked (by simpa only [Fits, Field.value, Lower.fits, Val.optionCheck, Field.armValue] using fits)
    | resultOk checked =>
      obtain ⟨_, next, admitted⟩ := armChild quirks encoding width checked
        (by simpa only [Fits, Field.value, Lower.fits, Val.resultCheck, Field.armValue] using fits)
      exact ih next admitted
    | resultError checked =>
      obtain ⟨_, next, admitted⟩ := armChild quirks encoding width checked
        (by simpa only [Fits, Field.value, Lower.fits, Val.resultCheck, Field.armValue] using fits)
      exact ih next admitted

private theorem recordPointer {types : List (String × TypeOf)} {fields : List Field} {child : Field}
    (certificate : Field.FieldsMatch fields (types.map Prod.snd)) (member : child ∈ fields)
    (pointer : ∀ {type}, child.LayoutMatches type → Validation.containsPtr type = true) :
    Validation.containsPtrFields types = true := by
  induction types generalizing fields with
  | nil => cases certificate; simp at member
  | cons _ _ ih =>
    cases certificate with
    | cons first rest =>
      apply Bool.or_eq_true_iff.mpr
      rcases List.mem_cons.mp member with rfl | tail
      · exact .inl (pointer first)
      · exact .inr (ih rest tail)

private theorem tuplePointer {types : List TypeOf} {fields : List Field} {child : Field}
    (certificate : Field.FieldsMatch fields types) (member : child ∈ fields)
    (pointer : ∀ {type}, child.LayoutMatches type → Validation.containsPtr type = true) :
    Validation.containsPtrList types = true := by
  induction types generalizing fields with
  | nil => cases certificate; simp at member
  | cons _ _ ih =>
    cases certificate with
    | cons first rest =>
      apply Bool.or_eq_true_iff.mpr
      rcases List.mem_cons.mp member with rfl | tail
      · exact .inl (pointer first)
      · exact .inr (ih rest tail)

private theorem casePointer {types : List (String × Option TypeOf)} {tag : Nat} {selected : Option TypeOf}
    (arm : (types.map Prod.snd)[tag]? = some selected)
    (pointer : Validation.containsPtrOpt selected = true) : Validation.containsPtrCases types = true := by
  induction types generalizing tag with
  | nil => simp at arm
  | cons head tail ih =>
    apply Bool.or_eq_true_iff.mpr
    cases tag with
    | zero =>
      have equal : head.2 = selected := by simpa using arm
      exact .inl (equal.symm ▸ pointer)
    | succ tag => exact .inr (ih (tag := tag) (by simpa using arm))

theorem descendantPointer {root child : Field} {type : TypeOf} (path : Field.Descendant root child)
    (certificate : root.LayoutMatches type) (pointer : Validation.containsPtr child.type = true) :
    Validation.containsPtr type = true := by
  induction path generalizing type with
  | self _ => exact certificate.type_eq ▸ pointer
  | aggregate member _ ih =>
    cases certificate with
    | record checked => exact recordPointer checked member (fun matched => ih matched pointer)
    | tuple checked => exact tuplePointer checked member (fun matched => ih matched pointer)
  | fixed member _ ih =>
    cases certificate with
    | fixed _ checked =>
      rw [Validation.containsPtr]
      exact ih (entriesMember checked member) pointer
  | dynamic _ _ _ => cases certificate <;> rfl
  | sum _ ih =>
    cases certificate with
    | variant arm checked => cases checked with | some payload => exact casePointer arm (ih payload pointer)
    | optionSome checked =>
      rw [Validation.containsPtr]
      exact ih checked pointer
    | resultOk checked => cases checked with | some payload => exact Bool.or_eq_true_iff.mpr (.inl (ih payload pointer))
    | resultError checked => cases checked with | some payload => exact Bool.or_eq_true_iff.mpr (.inr (ih payload pointer))

theorem descendantTrans {root child leaf : Field} (first : Field.Descendant root child)
    (second : Field.Descendant child leaf) : Field.Descendant root leaf := by
  induction first with
  | self _ => exact second
  | aggregate member _ ih => exact .aggregate member (ih second)
  | fixed member _ ih => exact .fixed member (ih second)
  | dynamic member _ ih => exact .dynamic member (ih second)
  | sum _ ih => exact .sum (ih second)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordAllocation
