(module
 (type $0 (func (param i32 i32) (result i32)))
 (global $count (mut i32) (i32.const 0))
 (export "sumsq" (func $sumsq))
 (export "mean" (func $mean))
 (export "ratio" (func $ratio))
 (func $sumsq (param $0 i32) (param $1 i32) (result i32)
  (global.set $count
   (i32.add
    (global.get $count)
    (i32.const 1)
   )
  )
  (global.set $count
   (i32.add
    (global.get $count)
    (i32.const 1)
   )
  )
  (i32.add
   (global.get $count)
   (i32.add
    (i32.mul
     (local.get $0)
     (local.get $0)
    )
    (i32.mul
     (local.get $1)
     (local.get $1)
    )
   )
  )
 )
 (func $mean (param $0 i32) (param $1 i32) (result i32)
  (i32.shr_u
   (i32.add
    (local.get $0)
    (local.get $1)
   )
   (i32.const 1)
  )
 )
 (func $ratio (param $0 i32) (param $1 i32) (result i32)
  (i32.add
   (i32.div_u
    (local.get $0)
    (local.get $1)
   )
   (i32.const 1)
  )
 )
)
