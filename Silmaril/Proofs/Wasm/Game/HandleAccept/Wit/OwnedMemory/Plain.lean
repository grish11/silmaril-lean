module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Value Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Formats
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

set_option maxHeartbeats 600000 in
mutual
theorem requirements_nil : ∀ (type : Stored.TypeOf) (value : Val),
    Stored.payloadContainsOwn type = false → ownerRequirements type value = []
  | .list element, value, plain | .fixedList element _, value, plain => by
    cases value <;> try rfl
    rename_i values
    apply List.flatMap_eq_nil_iff.mpr
    exact fun item _ => requirements_nil element item plain
  | .record types, value, plain => by
    cases value <;> first | rfl | exact fields_nil types _ plain
  | .tuple types, value, plain => by
    cases value <;> first | rfl | exact tuple_nil types _ plain
  | .variant types, value, plain => by
    cases value <;> first | rfl | exact cases_nil types _ _ plain
  | .option element, value, plain => by
    cases value <;> try rfl
    rename_i tag payload
    cases tag with
    | zero => rfl
    | succ index =>
      cases index <;> cases payload <;> first | rfl | exact requirements_nil element _ plain
  | .result success failure, value, plain => by
    have both : Stored.payloadOptContainsOwn success = false ∧
        Stored.payloadOptContainsOwn failure = false := Bool.or_eq_false_iff.mp plain
    cases value <;> try rfl
    rename_i tag payload
    cases tag with
    | zero => exact optional_nil success payload both.1
    | succ index =>
      cases index <;> first | rfl | exact optional_nil failure payload both.2
  | .map _ element, value, plain => by
    cases value <;> try rfl
    rename_i entries
    apply List.flatMap_eq_nil_iff.mpr
    intro entry _
    split
    · exact requirements_nil element _ plain
    · rfl
  | .own _, _, plain => by cases plain
  | .ref impossible, _, _ => nomatch impossible
  | .prim _, value, _ | .borrow _, value, _ | .flags _, value, _ | .enum _, value, _
    | .errorContext, value, _ | .stream _, value, _ | .future _, value, _ => by
    cases value <;> rfl
termination_by structural type => type

theorem fields_nil : ∀ (types : List (String × Stored.TypeOf)) (values : List Val),
    Stored.payloadFieldsContainOwn types = false → fieldRequirements types values = []
  | [], _, _ | (_, _) :: _, [], _ => rfl
  | (_, type) :: types, value :: values, plain => by
    have both : Stored.payloadContainsOwn type = false ∧
        Stored.payloadFieldsContainOwn types = false := Bool.or_eq_false_iff.mp plain
    simp only [fieldRequirements, requirements_nil type value both.1,
      fields_nil types values both.2, List.nil_append]
termination_by structural types => types

theorem tuple_nil : ∀ (types : List Stored.TypeOf) (values : List Val),
    Stored.payloadTypesContainOwn types = false → tupleRequirements types values = []
  | [], _, _ | _ :: _, [], _ => rfl
  | type :: types, value :: values, plain => by
    have both : Stored.payloadContainsOwn type = false ∧
        Stored.payloadTypesContainOwn types = false := Bool.or_eq_false_iff.mp plain
    simp only [tupleRequirements, requirements_nil type value both.1,
      tuple_nil types values both.2, List.nil_append]
termination_by structural types => types

theorem cases_nil : ∀ (cases : List (String × Option Stored.TypeOf)) (index : Nat)
    (value : Option Val), Stored.payloadCasesContainOwn cases = false →
    caseRequirements cases index value = []
  | [], _, _, _ => rfl
  | (_, type) :: cases, index, value, plain => by
    have both : Stored.payloadOptContainsOwn type = false ∧
        Stored.payloadCasesContainOwn cases = false := Bool.or_eq_false_iff.mp plain
    cases index with
    | zero => exact optional_nil type value both.1
    | succ index => exact cases_nil cases index value both.2
termination_by structural cases => cases

theorem optional_nil : ∀ (type : Option Stored.TypeOf) (value : Option Val),
    Stored.payloadOptContainsOwn type = false → optionalRequirements type value = []
  | none, _, _ | some _, none, _ => rfl
  | some type, some value, plain => requirements_nil type value plain
termination_by structural type => type
end

theorem requirements_of_schema {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ())
    (value : Val) : ownerRequirements type value = [] := by
  unfold Stored.checkSchema at admitted
  split at admitted
  · cases admitted
  · split at admitted
    · cases admitted
    · rename_i plain
      exact requirements_nil type value (Bool.eq_false_of_not_eq_true plain)

def payloadEquiv {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ()) :
    Stored.Payload type ≃ Payload type where
  toFun payload := ⟨Observed.ordinary payload.val, payload.property,
    (requirements_of_schema admitted payload.val).symm⟩
  invFun := Payload.erase
  left_inv _ := rfl
  right_inv payload := by
    have empty : payload.val.owners = [] := List.map_eq_nil_iff.mp
      (payload.property.2.trans (requirements_of_schema admitted payload.val.value))
    exact Subtype.ext (congrArg (Observed.mk payload.val.value) empty.symm)

theorem check_plain {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ())
    (value : Val) : checkValue type (Observed.ordinary value) =
      ((Stored.checkValue type value).map (payloadEquiv admitted)).mapError Issue.schema := by
  have empty := requirements_of_schema admitted value
  unfold checkValue Stored.checkValue Observed.ordinary
  split <;> simp_all [Except.map, Except.mapError, payloadEquiv, Observed.ordinary]

def treeEquiv (signature : PlainSignature) : Stored.Tree signature.val ≃ Tree signature.val where
  toFun := TExpr1.mapTag fun field => ⟨field.1, payloadEquiv (signature.property field.1) field.2⟩
  invFun := Tree.erase
  left_inv tree := by
    unfold Tree.erase
    rw [TExpr1.mapTag_comp]
    exact TExpr1.mapTag_id tree
  right_inv tree := by
    unfold Tree.erase
    rw [TExpr1.mapTag_comp]
    have identity : (fun (field : Σ tag, Payload (signature.val.payload tag)) =>
        (⟨field.1, payloadEquiv (signature.property field.1) field.2.erase⟩ :
          Σ tag, Payload (signature.val.payload tag))) = id := by
      funext field
      obtain ⟨tag, payload⟩ := field
      exact congrArg (Sigma.mk tag) ((payloadEquiv (signature.property tag)).right_inv payload)
    exact (congrArg (fun tagMap => TExpr1.mapTag tagMap tree) identity).trans (TExpr1.mapTag_id tree)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain
