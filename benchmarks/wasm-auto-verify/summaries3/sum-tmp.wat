(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $t i32) (local $acc i32)
  (block $done
   (loop $again
    (br_if $done (i32.eqz (local.get $n)))
    (local.set $t (i32.add (local.get $acc) (local.get $n)))
    (local.set $acc (local.get $t))
    (local.set $n (i32.sub (local.get $n) (i32.const 1)))
    (br $again)))
  (local.get $acc)))
