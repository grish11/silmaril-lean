(module
 (type $0 (func (param i32) (result i32)))
 (export "sum8" (func $sum8))
 (func $sum8 (param $0 i32) (result i32)
  (local $1 i32)
  (local $2 i32)
  (loop $l
   (local.set $2
    (i32.add
     (local.get $2)
     (i32.mul
      (local.get $0)
      (local.get $1)
     )
    )
   )
   (br_if $l
    (i32.lt_u
     (local.tee $1
      (i32.add
       (local.get $1)
       (i32.const 1)
      )
     )
     (i32.const 8)
    )
   )
  )
  (local.get $2)
 )
)
