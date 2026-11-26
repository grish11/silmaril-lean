module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity.Defs
public import Silmaril.Languages.Python.Core.Closure.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity

open Core.Closure (Heap Value)

theorem identify_empty (heap : Heap) : identify heap (.tuple []) = some .empty := rfl

theorem identify_allocation (heap : Heap) (head : Core.Module.TupleDispatch.Element) (tail : List Core.Module.TupleDispatch.Element) :
    let (cell, reached) := heap.allocate (.tuple (head :: tail))
    identify reached (.tupleObject ⟨some cell.address, head :: tail⟩) = some (.allocated cell.address) := by
  simp [identify, Heap.allocate, Heap.lookup, Heap.reserve]

theorem identify_savedOrigin (heap : Heap) (head : Core.Module.TupleDispatch.Element) (tail : List Core.Module.TupleDispatch.Element) :
    let (descriptor, reached) := heap.saveTupleOrigin head tail
    identify reached (.tupleObject descriptor) = some (.origin heap.next) := by
  simp [Heap.saveTupleOrigin, identify, Heap.allocate, Heap.lookup, Heap.reserve]

theorem identify_missing {heap : Heap} {address : Nat} (head : Core.Module.TupleDispatch.Element) (tail : List Core.Module.TupleDispatch.Element)
    (missing : heap.lookup ⟨address⟩ = none) :
    identify heap (.tupleObject ⟨some address, head :: tail⟩) = none := by
  simp [identify, missing]

theorem compare_identified (heap : Heap) (left right : Operand) (operator : Core.Module.IdentityOperator)
    {first second : Value} {one two : Identity}
    (identifiedFirst : identify heap first = some one) (identifiedSecond : identify heap second = some two) :
    (Test.mk left operator right).compare heap first second =
      (one.sameObject two).map (fun same => match operator with | .is_ => same | .isNot => !same) := by
  cases operator <;> simp [Test.compare, identifiedFirst, identifiedSecond]

theorem differentOrigins_unknown {first second : Nat} (different : first ≠ second) :
    (Identity.origin first).sameObject (.origin second) = none := by
  simp [Identity.sameObject, different]

theorem evaluate_same_origin {ε : Type} (heap : Heap) (lookup : String → Except ε (Option Value))
    (unsupported : ε) (left right : Operand) {value : Value} {address : Nat}
    (first : left.read lookup = .ok (some value)) (second : right.read lookup = .ok (some value))
    (found : identify heap value = some (.origin address)) :
    (Test.mk left .is_ right).evaluate heap lookup unsupported = .ok true := by
  simp [Test.evaluate, first, second, Bind.bind, Except.bind, Test.compare, found, Identity.sameObject]

theorem evaluate_left_failure {ε : Type} (test : Test) (heap : Heap)
    (lookup : String → Except ε (Option Value)) (unsupported : ε) {error : ε}
    (failed : test.left.read lookup = .error error) :
    test.evaluate heap lookup unsupported = .error error := by
  simp [Test.evaluate, failed]; rfl

theorem evaluate_right_failure {ε : Type} (test : Test) (heap : Heap)
    (lookup : String → Except ε (Option Value)) (unsupported : ε) {first : Option Value} {error : ε}
    (read : test.left.read lookup = .ok first) (failed : test.right.read lookup = .error error) :
    test.evaluate heap lookup unsupported = .error error := by
  simp [Test.evaluate, read, failed]; rfl

theorem evaluate_same_opaque_read {ε : Type} (heap : Heap) (lookup : String → Except ε (Option Value))
    (unsupported : ε) {name : String} {head : Core.Module.TupleDispatch.Element} {tail : List Core.Module.TupleDispatch.Element}
    (found : lookup name = .ok (some (.tuple (head :: tail)))) :
    (Test.mk (.global name) .is_ (.global name)).evaluate heap lookup unsupported = .ok true := by
  simp [Test.evaluate, Operand.read, found, Bind.bind, Except.bind, Test.compare, identify, sameOpaqueRead]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity
