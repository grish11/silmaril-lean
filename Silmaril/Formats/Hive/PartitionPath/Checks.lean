module

import Silmaril.Formats.Hive.PartitionPath.Thms
meta import Silmaril.Formats.Hive.PartitionPath.Defs

namespace Silmaril.Formats.Hive.PartitionPath

local instance {α : Type} [BEq α] : BEq (Except Error α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def defaults : Options := {}
private def required : Options := { requiredKeys := ["k", "n"] }
private def custom : Options := { nullMarker := "/none=" }

#guard parse required "n=__HIVE_DEFAULT_PARTITION__/k=a%2Fb=c%25" ==
    .ok [("n", none), ("k", some "a/b=c%")]

#guard parse defaults "x%3dy=%C3%A9/k=%252F/b=s+t/x=" ==
    .ok [("x=y", some "é"), ("k", some "%2F"), ("b", some "s+t"), ("x", some "")]

#guard parse defaults "k=%5f_HIVE_DEFAULT_PARTITION__" == .ok [("k", none)]
#guard parse custom "k=%2Fnone%3d" == .ok [("k", none)]
#guard parse defaults "" == .ok []
#guard parse defaults "/k=v" == .error .emptySegment
#guard parse defaults "k=v/" == .error .emptySegment
#guard parse defaults "k=v//x=y" == .error .emptySegment
#guard parse defaults "k=v/ordinary" == .error (.missingEquals "ordinary")
#guard parse defaults "k%3Dv" == .error (.missingEquals "k%3Dv")
#guard parse defaults "=v" == .error .emptyKey
#guard parse defaults "k=v/%6b=v" == .error (.duplicateKey "k")
#guard parse defaults "K=x/k=y" == .ok [("K", some "x"), ("k", some "y")]
#guard parse defaults "k=%" == .error .invalidEscape
#guard parse defaults "k=%A" == .error .invalidEscape
#guard parse defaults "k=%2G" == .error .invalidEscape
#guard parse defaults "k=%C3%28" == .error .invalidUtf8
#guard parse required "k=present" == .error (.missingKey "n")

#guard render defaults [("a/b=", some "é+%\\?#"), ("e", some ""), ("n", none)] ==
    .ok "a%2Fb%3D=%C3%A9%2B%25%5C%3F%23/e=/n=__HIVE_DEFAULT_PARTITION__"

#guard render custom [("n", none)] == .ok "n=%2Fnone%3D"
#guard render defaults [] == .ok ""
#guard render defaults [("", some "a")] == .error .emptyKey
#guard render required [("k", none)] == .error (.missingKey "n")
#guard render defaults [("k", none), ("k", some "")] == .error (.duplicateKey "k")

#guard render defaults [("k", some defaults.nullMarker)] ==
    .error (.nullMarkerCollision "k")

#guard parse { nullMarker := "" } "k=" == .error .emptyNullMarker
#guard render { nullMarker := "" } [("k", none)] == .error .emptyNullMarker

#guard lookup "x" [("n", none), ("e", some "")] == none
#guard lookup "n" [("n", none), ("e", some "")] == some none
#guard lookup "e" [("n", none), ("e", some "")] == some (some "")

#print axioms Percent.unescape_escape
#print axioms Percent.escape_safe
#print axioms Percent.decode_encode
#print axioms lookup_eq_some_iff
#print axioms parse_lookup

end Silmaril.Formats.Hive.PartitionPath
