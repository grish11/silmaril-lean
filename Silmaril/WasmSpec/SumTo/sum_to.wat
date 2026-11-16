(module
  ;; @requires true
  ;; @ensures (= result (tri n))
  (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32)
    (block $done
      (loop $again
        ;; @invariant (= (bvadd acc (tri n)) (tri (old n)))
        ;; @decreases n
        (br_if $done (i32.eqz (local.get $n)))
        (local.set $acc (i32.add (local.get $acc) (local.get $n)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $again)))
    (local.get $acc)))
