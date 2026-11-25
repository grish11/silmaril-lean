module

import SqliteWasm.ElementInit

open Silmaril.Wasm Silmaril.Wasm.Execution.Core SqliteWasm

example {H : Type} (s : Store H) (f : Frame) {decoded : Module}
    (bytes : Binary.Core.decode? originalBytes.toByteArray = some decoded)
    (addresses : f.module.funcs = List.range 1556) :
    evalExprss? evalConst? s f (decoded.elems.map Elem.init) = some (s, f, [reactorElementRefs]) := by
  have pinned : decoded = sqlite := Option.some.inj (bytes.symm.trans originalDecode)
  subst decoded
  exact reactorElementReplay s f addresses

example : reactorElementRefs.length = 342 := reactorElementRefsLength

example := reactorProvisionalElementReplay

#print axioms reactorElementRefsLength
#print axioms reactorElementReplay
#print axioms reactorProvisionalElementReplay
