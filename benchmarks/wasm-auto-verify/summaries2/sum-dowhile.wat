(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32)
  (if (local.get $n)
   (then
    (loop $again
     (local.set $acc (i32.add (local.get $acc) (local.get $n)))
     (local.set $n (i32.sub (local.get $n) (i32.const 1)))
     (br_if $again (local.get $n)))))
  (local.get $acc)))
