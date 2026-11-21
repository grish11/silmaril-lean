module

public import Silmaril.Wasm.Profiles.ISA.Defs

public section

namespace Silmaril.Proofs.Wasm.Profiles.ISA

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Profiles Silmaril.Wasm.Profiles.ISA

theorem lookup_opcode (tag : Flat) : Flat.lookup? tag.opcode = some tag := by cases tag <;> rfl

theorem lookup_some {opcode : Opcode} {tag : Flat} : Flat.lookup? opcode = some tag ↔ tag.opcode = opcode := by
  refine ⟨fun ok => ?_, fun eq => eq ▸ lookup_opcode tag⟩
  change Flat.all.find? (fun op => decide (op.opcode = opcode)) = some tag at ok
  exact of_decide_eq_true (List.find?_some (p := fun op : Flat => decide (op.opcode = opcode)) ok)

theorem admitted_lookup_some {W : Type} [HasFeatures W] {opcode : Opcode} {op : Admitted W} :
    Admitted.lookup? W opcode = some op ↔ op.val.opcode = opcode := by
  unfold Admitted.lookup?
  cases eq : Flat.lookup? opcode with
  | none =>
    change (none : Option (Admitted W)) = some op ↔ _
    constructor
    · intro hit
      cases hit
    · intro same
      have impossible : (none : Option Flat) = some op.val := eq.symm.trans (lookup_some.mpr same)
      cases impossible
  | some tag =>
    change (if ok : tag.use (HasFeatures.features W) then some ⟨tag, ok⟩ else none) = some op ↔ _
    constructor
    · split
      · intro same
        have sameTag := congrArg Subtype.val (Option.some.inj same)
        exact sameTag ▸ lookup_some.mp eq
      · simp
    · intro same
      have sameTag := Option.some.inj (eq.symm.trans (lookup_some.mpr same))
      subst tag
      simp [op.property]

theorem roundtrips {inputs outputs} (op : Op inputs outputs) :
    op.toFlat.toOp = op ∧ op.tag.pack = ⟨inputs, outputs, op⟩ := by
  cases op with
  | bin width op =>
    cases op with
    | add => cases width <;> exact ⟨rfl, rfl⟩
    | div sign => cases width <;> cases sign <;> exact ⟨rfl, rfl⟩
  | truncSat sign => cases sign <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem sound (ctx : Context) {inputs outputs} (op : Op inputs outputs) :
    InstrOk ctx op.erase (.plain inputs outputs) := by
  cases op with
  | bin width op => exact .numeric (.intBinOp width op.toCore)
  | extend32S64 => exact .numeric (.intUnOp rfl)
  | truncSat sign => exact .numeric (.convert (.truncSat .f32 .i32 sign))
  | refI31 => exact .reference .refI31

end Silmaril.Proofs.Wasm.Profiles.ISA
