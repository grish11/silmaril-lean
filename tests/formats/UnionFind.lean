module

import Silmaril.Formats.PER.UnionFind.Thms
meta import Silmaril.Formats.PER.UnionFind.Thms

open Silmaril.Formats.PER

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

public def main : IO Unit := do
  let start := ((UnionFind.singleton (10 : Nat)).insert 20 |>.insert 30).insert 40
  let some before := start.union 20 10 | throw (IO.userError "first union failed")
  check (before.sameClass 10 20 == some true && before.sameClass 10 30 == some false) "known answers"
  check ((before.sameClass 10 100).isNone && (before.union 10 100).isNone) "unknown is not false"
  check ((before.insert 10).find 10 == some 20) "insert known non-root is a no-op"
  let some forward := before.union 10 30 | throw (IO.userError "second union failed")
  let some backward := before.union 30 10 | throw (IO.userError "reversed union failed")
  check (forward.find 30 == some 20 && backward.find 20 == some 30) "left-biased representatives differ"
  check (forward.sameClass 20 30 == some true && backward.sameClass 20 30 == some true) "merged members agree"
  check (forward.sameClass 20 40 == some false && backward.sameClass 20 40 == some false) "third class unchanged"
  check (forward.find 100 == none && backward.find 100 == none) "support unchanged"
