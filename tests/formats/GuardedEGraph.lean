module

import Silmaril.Formats.PER.EGraph.Thms
meta import Silmaril.Formats.PER.EGraph.Defs

open Silmaril.Formats.PER.EGraph

private def terms : Array (Node String Nat) :=
  #[⟨"a", []⟩, ⟨"b", []⟩, ⟨"c", []⟩, ⟨"f", [0, 2]⟩, ⟨"f", [1, 2]⟩, ⟨"f", [2, 1]⟩, ⟨"f", [1]⟩]

private def expect (success : Bool) (label : String) : IO Unit :=
  unless success do throw (IO.userError label)

public def main : IO Unit := do
  expect ((checkDag? (#[⟨"f", [1]⟩, ⟨"g", [0]⟩] : Array (Node String Nat))).isNone) "term cycle"
  expect ((checkDag? (#[⟨"f", [8]⟩] : Array (Node String Nat))).isNone) "dangling child"
  let some dag := checkDag? terms | throw (IO.userError "ordered DAG rejected")
  let idAt := fun value => termId? dag.val.size value
  let some termA := idAt 0 | throw (IO.userError "missing a")
  let some termB := idAt 1 | throw (IO.userError "missing b")
  let some termC := idAt 2 | throw (IO.userError "missing c")
  let some termFA := idAt 3 | throw (IO.userError "missing f(a,c)")
  let some termFB := idAt 4 | throw (IO.userError "missing f(b,c)")
  let some reversed := idAt 5 | throw (IO.userError "missing f(c,b)")
  let some unary := idAt 6 | throw (IO.userError "missing f(b)")
  let partition := fun classOf => (⟨dag.val.size, classOf⟩ : Partition dag.val.size)
  let seeds : Seeds dag.val.size := fun left right => left == termA && right == termB
  let initial := partition id
  let seeded := partition fun id => if id = termB then termA else id
  let rebuilt := partition fun id => if id = termFB then termFA else seeded.classOf id
  let tooCoarse := partition fun _ => termA
  let dropsSeed := partition fun id => if id = termFB then termFA else id
  expect (initial.lookup 7).isNone "raw term guard"
  expect (decide (dag.Rebuilt initial)) "discrete signatures are distinct"
  expect ((dag.merge? seeds initial seeded termA termC .seed).isNone) "not an asserted seed"
  expect ((dag.merge? seeds initial tooCoarse termA termB .seed).isNone) "unauthorized extra equalities"
  expect ((dag.merge? seeds initial seeded termA termB .seed).isSome) "asserted seed"
  expect (!(decide (dag.Rebuilt seeded))) "seed invalidates signature coherence"
  expect ((dag.merge? seeds initial rebuilt termFA termFB .collision).isNone) "children not yet equal"
  expect ((dag.merge? seeds seeded rebuilt termFA reversed .collision).isNone) "child order matters"
  expect ((dag.merge? seeds seeded rebuilt termFA unary .collision).isNone) "child arity matters"
  expect ((dag.merge? seeds seeded dropsSeed termFA termFB .collision).isNone) "cannot split an old class"
  expect ((dag.merge? seeds seeded rebuilt termFA termFB .collision).isSome) "valid rebuild"
  expect (decide (dag.Rebuilt rebuilt)) "signatures are coherent after the rebuild"
  expect ((dag.merge? seeds rebuilt rebuilt termFA termFB .collision).isNone) "already coherent collision"
  let cyclic := partition fun id => if id = termFA then termA else id
  let cycleSeed : Seeds dag.val.size := fun left right => left == termA && right == termFA
  expect ((dag.merge? cycleSeed initial cyclic termA termFA .seed).isSome) "term DAG can witness a cyclic e-class graph"
