(module
 (type $0 (func (param i32) (result i32)))
 (export "sum" (func $sum))
 (func $sum (param $0 i32) (result i32)
  (local $1 i32)
  (loop $again
   (if
    (local.get $0)
    (then
     (local.set $1
      (i32.add
       (i32.add
        (local.get $1)
        (local.tee $0
         (i32.sub
          (local.get $0)
          (i32.const 1)
         )
        )
       )
       (i32.const 1)
      )
     )
     (br $again)
    )
   )
  )
  (local.get $1)
 )
)
