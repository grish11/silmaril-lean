module

public import Silmaril.Formats.Dasl.RawStore.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.RawStore

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.RawStore Silmaril.Semantics.Naming

variable {Name : Type} {decoder : Decoder Name} {base defaults extended policy : Blocks Name}

theorem readObject_found_iff {read : Wire.Cid → Option ByteArray} {name : Wire.Cid} {value : Shallow Wire.Cid} :
    Wire.readObject read name = .found value ↔ Wire.IsObjectCid name ∧
      ∃ bytes, graph read name bytes ∧ Wire.parse? bytes = some value := by
  simp only [Wire.readObject, beq_iff_eq, Wire.IsObjectCid]
  by_cases object : name.val[1]? = some 0x71
  · cases hit : read name with
    | none => simp [object, graph, hit]
    | some bytes => cases parsed : Wire.parse? bytes <;> simp [object, graph, hit, parsed]
  · simp [object]

theorem readObject_missing_iff {read : Wire.Cid → Option ByteArray} {name : Wire.Cid} :
    Wire.readObject read name = .missing ↔ Wire.IsObjectCid name ∧ read name = none := by
  simp only [Wire.readObject, beq_iff_eq, Wire.IsObjectCid]
  by_cases object : name.val[1]? = some 0x71
  · cases hit : read name with
    | none => simp [object]
    | some bytes => cases parsed : Wire.parse? bytes <;> simp [object, parsed]
  · simp [object]

theorem readObject_invalidWire_iff {read : Wire.Cid → Option ByteArray} {name : Wire.Cid} :
    Wire.readObject read name = .invalidWire ↔ ¬ Wire.IsObjectCid name ∨
      ∃ bytes, read name = some bytes ∧ Wire.parse? bytes = none := by
  simp only [Wire.readObject, beq_iff_eq, Wire.IsObjectCid]
  by_cases object : name.val[1]? = some 0x71
  · cases hit : read name with
    | none => simp [object]
    | some bytes => cases parsed : Wire.parse? bytes <;> simp [object, parsed]
  · simp [object]

theorem view_binding (bound : Binding base) : (decoder.view base).Binding := by
  constructor
  · rintro name left right ⟨_, bytes, read, parsed⟩ ⟨_, other, read', parsed'⟩
    cases bound read read'
    exact Option.some.inj (parsed.symm.trans parsed')
  · intro name left right read read'
    exact bound read.2 read'.2

theorem completion_iff {root : Name} : Completes decoder policy base extended root ↔
    Subset base extended ∧ Binding extended ∧ Subset extended policy ∧
      (∃ source, (decoder.view extended).objects root source) ∧
      Acc (Depends (decoder.view extended)) root ∧ ClosedBelow (decoder.view extended) root := by
  constructor <;> rintro ⟨preserve, bound, allowed, rest⟩
  · exact ⟨preserve, bound, allowed, (full_exists_iff (view_binding bound) root).mp rest⟩
  · exact ⟨preserve, bound, allowed, (full_exists_iff (view_binding bound) root).mpr rest⟩

theorem fill_completes {root : Name} (baseBound : Binding base) (defaultBound : Binding defaults)
    (baseAllowed : Subset base policy)
    (defaultAllowed : ∀ ⦃name bytes⦄, (¬ ∃ old, base name old) → defaults name bytes → policy name bytes)
    (found : ∃ source, (decoder.view (fill base defaults)).objects root source)
    (access : Acc (Depends (decoder.view (fill base defaults))) root)
    (closed : ClosedBelow (decoder.view (fill base defaults)) root) : Completes decoder policy base (fill base defaults) root := by
  refine completion_iff.mpr ⟨subset_fillMissing, fillMissing_binding baseBound defaultBound, ?_, found, access, closed⟩
  rintro name bytes (hit | ⟨absent, supplied⟩)
  · exact baseAllowed hit
  · exact defaultAllowed absent supplied

theorem no_completion_of_malformed_root {root : Name} {bytes : ByteArray}
    (present : base root bytes) (malformed : decoder.parse? bytes = none) :
    ¬ Completes decoder policy base extended root := by
  rintro ⟨preserve, bound, _, target, source, ⟨_, other, read, parsed⟩, _⟩
  cases bound (preserve present) read
  simp [malformed] at parsed

theorem no_completion_of_self_link {root : Name} {bytes : ByteArray} {source : Shallow Name}
    (present : base root bytes) (codec : decoder.objectName root)
    (parsed : decoder.parse? bytes = some source) (linked : Link.obj root ∈ source.directLinks) :
    ¬ Completes decoder policy base extended root := by
  intro completed
  have requirements := completion_iff.mp completed
  have loop : Depends (decoder.view extended) root root :=
    ⟨source, ⟨codec, bytes, requirements.1 present, parsed⟩, linked⟩
  have notSelf {rel : Name → Name → Prop} {name : Name} (accessible : Acc rel name) : ¬ rel name name := by
    induction accessible with
    | intro name _ ih => intro edge; exact ih name edge edge
  exact notSelf requirements.2.2.2.2.1 loop

end Silmaril.Proofs.Formats.Dasl.RawStore
