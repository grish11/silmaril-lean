(module
 (type $0 (func (param i32) (result i32)))
 (export "sum" (func $sum))
 (func $sum (param $0 i32) (result i32)
  (local $1 i32)
  (if
   (local.get $0)
   (then
    (loop $again
     (local.set $1
      (i32.add
       (local.get $0)
       (local.get $1)
      )
     )
     (br_if $again
      (local.tee $0
       (i32.sub
        (local.get $0)
        (i32.const 1)
       )
      )
     )
    )
   )
  )
  (local.get $1)
 )
)
