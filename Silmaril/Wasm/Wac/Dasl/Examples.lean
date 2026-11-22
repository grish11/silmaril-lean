module

import Silmaril.Wasm.Wac.Dasl.Thms
import Silmaril.Wasm.Component.Binary.Encode.Defs
import Silmaril.Formats.Dasl.Wire.Defs
meta import Silmaril.Wasm.Wac.Dasl.Thms
meta import Silmaril.Formats.Dasl.Wire.Defs

namespace Silmaril.Wasm.Wac.Dasl.Examples

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming
open Silmaril.Formats.Cbor

private def functionType : Component.FuncTy := ⟨[], [.u32]⟩

private def component (input output : String) : Component.Binary.Ast := .mk [
  .types [.func ⟨[], some (.prim .u32), false⟩],
  .imports [⟨⟨input, .plain0⟩, .func 0⟩],
  .exports [⟨⟨output, .plain0⟩, ⟨.func, 0⟩, none⟩]]

private def providerBytes : ByteArray := (Component.Binary.encode (component "seed" "greet")).getD ⟨#[]⟩
private def consumerBytes : ByteArray := (Component.Binary.encode (component "greet" "run")).getD ⟨#[]⟩

example : (Component.Binary.parse providerBytes).toOption.isSome = true := by decide +kernel
example : (Component.Binary.parse consumerBytes).toOption.isSome = true := by decide +kernel

private def provider : PkgSig := ⟨[("seed", functionType)], [("greet", functionType)]⟩
private def consumer : PkgSig := ⟨[("greet", functionType)], [("run", functionType)]⟩

private def wiring : Graph where
  imports := [("seed", functionType)]
  nodes := [⟨0, [("seed", .imp "seed")]⟩, ⟨1, [("greet", .out 0 "greet")]⟩]
  exports := [("run", .out 1 "run")]

private def value : Composition (Nat × ByteArray) :=
  ⟨wiring, [(provider, 10, providerBytes), (consumer, 11, consumerBytes)]⟩

example : value.Resolved := by
  constructor
  · intro inst hit
    simp [value, wiring] at hit ⊢
    rcases hit with rfl | rfl <;> decide
  · constructor
    · intro index inst hit
      have bound : index < 2 := (List.getElem?_eq_some_iff.mp hit).choose
      have cases : index = 0 ∨ index = 1 := by omega
      rcases cases with rfl | rfl
      · cases hit
        intro arg member
        simp [value, provider] at member
        subst arg
        exact List.mem_cons_self
      · cases hit
        intro arg member
        simp [value, consumer] at member
        subst arg
        exact ⟨_, rfl, by decide, by decide⟩
    · intro item member
      simp [value, wiring] at member
      subst item
      exact ⟨_, rfl, by decide, by decide⟩

private def fixture (complete : Bool) : Store Nat where
  objects := Silmaril.Semantics.Naming.graph (fun | 0 => some (shallow.encode value.names) | _ => none)
  blobs := Silmaril.Semantics.Naming.graph
    (fun | 10 => some providerBytes | 11 => if complete then some consumerBytes else none | _ => none)

private theorem fixture_binding (complete : Bool) : (fixture complete).Binding := by
  constructor <;> intro _ _ _ first second <;> exact Option.some.inj (first.symm.trans second)

example : ExpandedNames (fixture true) 0 value := by
  apply recovered value rfl
  intro row member
  simp [value] at member
  rcases member with rfl | rfl <;> rfl

example : ¬ ∃ tree, FullNames (fixture false) 0 tree := by
  intro full
  have direct : Link.blob 11 ∈ (shallow.encode value.names).directLinks :=
    ⟨1, 1, ⟨1, Nat.one_lt_two⟩, 1, rfl⟩
  have closed := (full_exists_iff (fixture_binding false) 0).1 full |>.2.2
  obtain ⟨_, impossible⟩ := (closed .refl (show (fixture false).objects 0 (shallow.encode value.names) from rfl)).2 11 direct
  cases impossible

/-! Synthetic BLAKE3-shaped digests are names, not hashes of the bytes above. -/

private abbrev Cid := Drisl.Cid .bdasl

private def providerCid : Cid := ⟨[1, 0x55, 0x1e, 32] ++ List.replicate 32 17, by decide⟩
private def consumerCid : Cid := ⟨[1, 0x55, 0x1e, 32] ++ List.replicate 32 34, by decide⟩
private def objectCid : Cid := ⟨[1, 0x71, 0x1e, 32] ++ List.replicate 32 51, by decide⟩

private def typedValue : Composition Cid := ⟨wiring, [(provider, providerCid), (consumer, consumerCid)]⟩

example : (Wire.cidCodecFor .bdasl).parse? providerCid.val = some (.blob providerCid) := by decide +kernel
example : (Wire.cidCodecFor .bdasl).parse? objectCid.val = some (.obj objectCid) := by decide +kernel
example : Wire.cidCodec.parse? providerCid.val = none := by decide +kernel
example : rawLink.decode? (.ref (.obj objectCid)) = none := rfl

private def bdaslRoundtrip : Option (Graph × List Cid) := do
  let codec := Wire.cidCodecFor .bdasl
  let bytes ← Drisl.renderCbor? Drisl.i64Cbor codec (Wire.toOrdered (shallow.encode typedValue))
  let wire ← Drisl.parseCbor? Drisl.i64Cbor codec bytes
  let decoded ← shallow.decode? (Wire.lower wire)
  pure (decoded.graph, decoded.packages.map Prod.snd)

#guard decide (bdaslRoundtrip = some (wiring, [providerCid, consumerCid]))

end Silmaril.Wasm.Wac.Dasl.Examples
