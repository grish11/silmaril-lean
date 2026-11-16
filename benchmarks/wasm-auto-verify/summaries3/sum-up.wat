(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32) (local $i i32)
  (block $done
   (loop $again
    (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
    (local.set $i (i32.add (local.get $i) (i32.const 1)))
    (local.set $acc (i32.add (local.get $acc) (local.get $i)))
    (br $again)))
  (local.get $acc)))
