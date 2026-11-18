(module
 (type $0 (func (param i32 i32) (result i32)))
 (export "divsum4" (func $divsum4))
 (func $divsum4 (param $0 i32) (param $1 i32) (result i32)
  (local $2 i32)
  (local $3 i32)
  (loop $l
   (local.set $3
    (i32.add
     (local.get $3)
     (i32.div_u
      (local.get $0)
      (i32.add
       (local.get $1)
       (local.get $2)
      )
     )
    )
   )
   (br_if $l
    (i32.lt_u
     (local.tee $2
      (i32.add
       (local.get $2)
       (i32.const 1)
      )
     )
     (i32.const 4)
    )
   )
  )
  (local.get $3)
 )
)
