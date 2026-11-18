(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32) (local $i i32)
  (local.set $i (local.get $n))
  (if (local.get $i)
   (then
    (loop $again
     (local.set $acc (i32.add (local.get $i) (local.get $acc)))
     (br_if $again (local.tee $i (i32.sub (local.get $i) (i32.const 1)))))))
  (local.get $acc)))
