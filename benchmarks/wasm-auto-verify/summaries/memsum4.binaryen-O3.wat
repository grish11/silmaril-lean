(module
 (type $0 (func (param i32) (result i32)))
 (memory $0 1)
 (data $0 (i32.const 0) "\01\02\03\04\05\06\07\08")
 (export "memsum4" (func $memsum4))
 (func $memsum4 (param $0 i32) (result i32)
  (local $1 i32)
  (local $2 i32)
  (loop $l
   (local.set $2
    (i32.add
     (local.get $2)
     (i32.load8_u
      (i32.add
       (local.get $0)
       (local.get $1)
      )
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
     (i32.const 4)
    )
   )
  )
  (local.get $2)
 )
)
