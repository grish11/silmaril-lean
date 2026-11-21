module

import Silmaril.Semantics.Arena.Thms

namespace Silmaril.Semantics.Arena.Examples

private def blank : Slot Nat ByteArray := ⟨none, none⟩
private def bytes : ByteArray := ByteArray.mk #[1, 2]
private def initial : Dense 2 Nat ByteArray := ⟨#[some blank, none], rfl⟩

example : initial.read 0 = some blank ∧ initial.read 1 = none := ⟨rfl, rfl⟩

example : (initial.step 0 (.reserve none)).map (·.read 0) = .error .occupied := rfl
example : (initial.step 1 (.write (fun _ => none) bytes)).map (·.read 1) = .error .vacant := rfl
example : (initial.step 2 (.reserve none)).map (·.read 2) = .error .outOfBounds := rfl

private def lifecycle : Except Fault (List (Option (Slot Nat ByteArray))) := do
  let reserved ← initial.step 1 (.reserve (some 10))
  let named ← reserved.step 1 (.write (fun _ => some 11) bytes)
  let erased ← named.step 1 .erasePayload
  let anonymous ← erased.step 1 (.write (fun _ => none) bytes)
  let cleared ← anonymous.step 1 .clear
  let grown := cleared.append blank
  pure [reserved.read 1, named.read 1, erased.read 1, anonymous.read 1, grown.read 1, grown.read 2, grown.read 0]

example : lifecycle = .ok [some ⟨some 10, none⟩, some ⟨some 11, some bytes⟩, some ⟨some 11, none⟩,
    some ⟨none, some bytes⟩, none, some blank, some blank] := rfl

private def reserved : ByteState String Nat := fun key => if key = "root" then some ⟨some 10, none⟩ else none
private def replaced : ByteState String Nat := reserved.replaceAt "root" (some ⟨some 10, some bytes⟩)

example : reserved.keyName "root" = some 10 := rfl

example : reserved.step "root" (.write (fun _ => some 10) bytes) = .ok replaced := rfl

example : ¬ replaced.AdmittedBy (fun _ _ => False) :=
  fun admitted => admitted (name := 10) (payload := bytes) ⟨"root", rfl⟩

end Silmaril.Semantics.Arena.Examples
