module

public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-! # Exits of the structured contexts of Core 3.0

A `LABEL`, `HANDLER` or `FRAME` configuration steps either inside (`ctxt-label`,
`ctxt-handler`, `ctxt-frame`) or by one of the rules that remove the context. These
relations list the removing rules, each with exactly the premises of its `Step`
constructor: `LabelExit n cont is out` says that `[LABEL_n{cont} is]` reduces to `out` by
an exit rule, with the store and frame unchanged (and similarly for the others). The
inversion theorems are in `Inversion/Thms.lean`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- The rules that leave `LABEL_n{cont} is` (store and frame unchanged). -/
inductive LabelExit (n : Nat) (cont : List Instr) : List Admin → List Admin → Prop where
  /-- `label-vals`. -/
  | vals (vs : List Val) : LabelExit n cont (vals vs) (vals vs)
  /-- `br-label-zero`: the continuation runs on the top `n` values. -/
  | brZero {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0)
      (hn : vs.length = n) :
      LabelExit n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) (vals vs ++ expression cont)
  /-- `br-label-succ`. -/
  | brSucc {vs : List Val} {l : LabelIdx} {rest : List Admin} (hl : 0 < l.toNat) :
      LabelExit n cont (vals vs ++ [.plain (.br l)] ++ rest) (vals vs ++ [.plain (.br (labelPred l))])
  /-- `return-label`. -/
  | ret {vs : List Val} {rest : List Admin} :
      LabelExit n cont (vals vs ++ [.plain .return_] ++ rest) (vals vs ++ [.plain .return_])
  /-- `return_call_ref-label`. -/
  | returnCall {vs : List Val} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      LabelExit n cont (vals vs ++ [c] ++ rest) (vals vs ++ [c])
  /-- `throw_ref-label`. -/
  | throw (a : Nat) : LabelExit n cont (throwing a) (throwing a)
  /-- `trap-label`. -/
  | trap : LabelExit n cont [.trap] [.trap]

/-- The rules that leave `HANDLER_n{cs} is` (store and frame unchanged), including the
`throw_ref-handler-*` rules that catch or pass on an exception. -/
inductive HandlerExit (s : Store H) (f : Frame) (n : Nat) :
    List Catch → List Admin → List Admin → Prop where
  /-- `handler-vals`. -/
  | vals {cs : List Catch} (vs : List Val) : HandlerExit s f n cs (vals vs) (vals vs)
  /-- `br-handler`. -/
  | br {cs : List Catch} {vs : List Val} {l : LabelIdx} {rest : List Admin} :
      HandlerExit s f n cs (vals vs ++ [.plain (.br l)] ++ rest) (vals vs ++ [.plain (.br l)])
  /-- `return-handler`. -/
  | ret {cs : List Catch} {vs : List Val} {rest : List Admin} :
      HandlerExit s f n cs (vals vs ++ [.plain .return_] ++ rest) (vals vs ++ [.plain .return_])
  /-- `return_call_ref-handler`. -/
  | returnCall {cs : List Catch} {vs : List Val} {c : Admin} {rest : List Admin}
      (hc : c.IsReturnCallRef) : HandlerExit s f n cs (vals vs ++ [c] ++ rest) (vals vs ++ [c])
  /-- `trap-handler`. -/
  | trap {cs : List Catch} : HandlerExit s f n cs [.trap] [.trap]
  /-- `throw_ref-handler-empty`. -/
  | throwEmpty (a : Nat) : HandlerExit s f n [] (throwing a) (throwing a)
  /-- `throw_ref-handler-catch`. -/
  | catch_ {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      HandlerExit s f n (.catch_ x l :: cs) (throwing a) (vals e.fields ++ [.plain (.br l)])
  /-- `throw_ref-handler-catch_ref`. -/
  | catchRef {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      HandlerExit s f n (.catchRef x l :: cs) (throwing a)
        (vals e.fields ++ [.ref (.exn a), .plain (.br l)])
  /-- `throw_ref-handler-catch_all`. -/
  | catchAll {l : LabelIdx} {cs : List Catch} (a : Nat) :
      HandlerExit s f n (.catchAll l :: cs) (throwing a) [.plain (.br l)]
  /-- `throw_ref-handler-catch_all_ref`. -/
  | catchAllRef {l : LabelIdx} {cs : List Catch} (a : Nat) :
      HandlerExit s f n (.catchAllRef l :: cs) (throwing a) [.ref (.exn a), .plain (.br l)]
  /-- `throw_ref-handler-next`: the handler stays, with its first clause dropped. -/
  | next {c : Catch} {cs : List Catch} {a : Nat} (h : ¬ CatchMatches s f a c) :
      HandlerExit s f n (c :: cs) (throwing a) [.handler n cs (throwing a)]

/-- The rules that leave `FRAME_n{fi} is` (store unchanged; the result runs in the outer
frame, whatever it is): values, `return`, a trap, an exception, a tail call. -/
inductive FrameExit (s : Store H) (fi : Frame) (n : Nat) : List Admin → List Admin → Prop where
  /-- `frame-vals`. -/
  | vals {vs : List Val} (hn : vs.length = n) : FrameExit s fi n (vals vs) (vals vs)
  /-- `return-frame`. -/
  | ret {vs' vs : List Val} {rest : List Admin} (hn : vs.length = n) :
      FrameExit s fi n (vals vs' ++ vals vs ++ [.plain .return_] ++ rest) (vals vs)
  /-- `trap-frame`. -/
  | trap : FrameExit s fi n [.trap] [.trap]
  /-- `throw_ref-frame`. -/
  | throw (a : Nat) : FrameExit s fi n (throwing a) (throwing a)
  /-- `return_call_ref-frame-null`. -/
  | returnCallNull {vs : List Val} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      FrameExit s fi n (vals vs ++ [.ref .null, c] ++ rest) [.trap]
  /-- `return_call_ref-frame-addr`. -/
  | returnCallAddr {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
      {ps rs : Ty (.list .val)} (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn)
      (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) :
      FrameExit s fi n (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)
        (vals vs ++ [.ref (.func a), c.retToCallIn fi.module])

/-- `loop bt (br 0)` about to be entered: the smallest non-terminating body. -/
abbrev loopBr0 (s : Store H) (f : Frame) (bt : BlockType) : Config H :=
  ⟨s, f, [.plain (.loop bt [.br ⟨0⟩])]⟩

/-- `loop bt (br 0)` entered: its label around the body `br 0`. -/
abbrev labelBr0 (s : Store H) (f : Frame) (bt : BlockType) : Config H :=
  ⟨s, f, [.label 0 [.loop bt [.br ⟨0⟩]] [.plain (.br ⟨0⟩)]]⟩

end Silmaril.Wasm.Execution.Core

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

variable {H : Type}

/-- A step by one of the eight non-control reduction families of `Step` (no context rule). -/
inductive FamStep (P : Profile) : Config H → Config H → Prop where
  | parametric {s : Store H} {f : Frame} {is is' : List Admin} (h : ParametricStep is is') :
      FamStep P ⟨s, f, is⟩ ⟨s, f, is'⟩
  | numeric {s : Store H} {f : Frame} {is is' : List Admin} (h : NumericStep P is is') :
      FamStep P ⟨s, f, is⟩ ⟨s, f, is'⟩
  | vector {s : Store H} {f : Frame} {is is' : List Admin} (h : VectorStep P is is') :
      FamStep P ⟨s, f, is⟩ ⟨s, f, is'⟩
  | «variable» {c c' : Config H} (h : VariableStep c c') : FamStep P c c'
  | table {c c' : Config H} (h : TableStep P c c') : FamStep P c c'
  | memory {c c' : Config H} (h : MemoryStep P c c') : FamStep P c c'
  | reference {c c' : Config H} (h : RefStep c c') : FamStep P c c'
  | aggregate {c c' : Config H} (h : AggregateStep c c') : FamStep P c c'

end Silmaril.Wasm.Execution.Core
