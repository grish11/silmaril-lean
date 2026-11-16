module

public import Silmaril.Proofs.Wasm.Cfg.Region
public import Silmaril.Wasm.Abstract.CallX.Defs

@[expose] public section

/-!
# The region semantics resolves tail calls as `CallX.TailRes` does

A tail call that `CallX.TailRes` resolves to a callee (direct, indirect through the table and
the cast, or by reference) runs in the region semantics to a pending tail call of that callee,
over the values under its operands. An unresolved one runs to a trap, or, on a null reference
(directly or from the table), to a pending tail call of null.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallRes
open Silmaril.Wasm.SingleThreaded (Det.famOf)

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem tableGet_steps {s : Store H} {f : Frame} {W : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst} {r : Ref}
    (ht : s.table? f x = some (ta, ti)) (hr : ti.refs[i.toNat]? = some r) :
    Steps P host ⟨s, f, vals (W ++ [.num ⟨.int a.intType, i⟩]) ++ [.plain (.tableGet x)]⟩
      ⟨s, f, vals (W ++ [.ref r])⟩ := by
  have := step_in (P := P) (host := host) W [] (Step.table (TableStep.getVal (P := P) ht hr))
  exact .single (by simpa [vals, Val.toAdmin] using this)

theorem tableGet_trap {s : Store H} {f : Frame} {W : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (hl : ti.refs.length ≤ i.toNat) :
    Steps P host ⟨s, f, vals (W ++ [.num ⟨.int a.intType, i⟩]) ++ [.plain (.tableGet x)]⟩
      ⟨s, f, [.trap]⟩ := by
  have h1 := step_in (P := P) (host := host) W [] (Step.table (TableStep.getOob (P := P) ht hl))
  exact (Relation.ReflTransGen.single (by simpa [vals, Val.toAdmin] using h1)).trans
    (by simpa [vals] using steps_trap (P := P) (host := host) s f W [])

theorem refCast_steps {s : Store H} {f : Frame} {W : List Val} {r : Ref} {rt : RefType}
    (hc : RefOk s r (f.module.instRef rt)) :
    Steps P host ⟨s, f, vals (W ++ [.ref r]) ++ [.plain (.refCast rt)]⟩
      ⟨s, f, vals (W ++ [.ref r])⟩ := by
  have := step_in (P := P) (host := host) W [] (Step.reference (RefStep.castSucceed hc))
  exact .single (by simpa [vals, Val.toAdmin] using this)

theorem refCast_trap {s : Store H} {f : Frame} {W : List Val} {r : Ref} {rt : RefType}
    (hc : ¬ RefOk s r (f.module.instRef rt)) :
    Steps P host ⟨s, f, vals (W ++ [.ref r]) ++ [.plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩ := by
  have h1 := step_in (P := P) (host := host) W [] (Step.reference (RefStep.castFail hc))
  exact (Relation.ReflTransGen.single (by simpa [vals, Val.toAdmin] using h1)).trans
    (by simpa [vals] using steps_trap (P := P) (host := host) s f W [])

theorem famOf_tableGet (x : TableIdx) : Det.famOf (.plain (.tableGet x)) ≠ .control := by
  simp [Det.famOf]

theorem famOf_refCast (rt : RefType) : Det.famOf (.plain (.refCast rt)) ≠ .control := by
  simp [Det.famOf]

/-- **A resolved tail call is a pending tail call of the resolved callee.** On the stack `stk`
(top first, as `TailRes` reads it) above `W`, the terminator runs to `Out.tail W a c`. -/
theorem run_of_tailRes {s : Store H} {f : Frame} {i : Instr} {stk : List Val} {a : Nat}
    (W : List Val) (h : TailRes s f i stk (some (a, stk.drop (tailPop i)))) :
    ∃ c, c.IsReturnCallRef ∧
      RunC P host C s f (W ++ (stk.take (tailPop i)).reverse) [.plain i] s f (.tail W a c) := by
  cases h with
  | @direct x a fi stk hfi =>
    refine ⟨.returnCallRefType fi.type, trivial, ?_⟩
    simpa [tailPop] using RunC.returnCall (P := P) (host := host) (C := C) (vs := W) (code := []) hfi
  | @ref y _ stk' =>
    refine ⟨.plain (.returnCallRef y), trivial, ?_⟩
    simpa [tailPop] using RunC.returnCallRef (P := P) (host := host) (C := C) (s := s) (f := f)
      (ws := W) (a := a) (code := []) (c := .plain (.returnCallRef y)) trivial
  | @indirect x y ad n fa stk' hres =>
    cases hres with
    | func ht hr hc =>
      refine ⟨.plain (.returnCallRef y), trivial, ?_⟩
      simp only [tailPop, List.take_succ_cons, List.take_zero, List.reverse_cons,
        List.reverse_nil, List.nil_append]
      exact .returnCallIndirect (.simple (famOf_tableGet x) (tableGet_steps ht hr)
        (.simple (famOf_refCast _) (refCast_steps hc)
          (.returnCallRef (ws := W) (c := .plain (.returnCallRef y)) trivial)))

/-- **An unresolved tail call** traps, or is a pending tail call of null (a null reference,
directly or from the table). -/
theorem run_of_tailRes_none {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    (W : List Val) (h : TailRes s f i stk none) :
    RunC P host C s f (W ++ (stk.take (tailPop i)).reverse) [.plain i] s f .trap ∨
      ∃ c, c.IsReturnCallRef ∧
        RunC P host C s f (W ++ (stk.take (tailPop i)).reverse) [.plain i] s f (.tailNull W c) := by
  cases h with
  | @refNull y stk' =>
    refine .inr ⟨.plain (.returnCallRef y), trivial, ?_⟩
    simpa [tailPop] using RunC.returnCallRefNull (P := P) (host := host) (C := C) (s := s)
      (f := f) (ws := W) (code := []) (c := .plain (.returnCallRef y)) trivial
  | @indirectTrap x y ad n stk' hres =>
    simp only [tailPop, List.take_succ_cons, List.take_zero, List.reverse_cons,
      List.reverse_nil, List.nil_append]
    cases hres with
    | oob ht hl =>
      exact .inl (.returnCallIndirect (.simpleTrap (famOf_tableGet x) (tableGet_trap ht hl)))
    | castFail ht hr hc =>
      exact .inl (.returnCallIndirect (.simple (famOf_tableGet x) (tableGet_steps ht hr)
        (.simpleTrap (famOf_refCast _) (refCast_trap hc))))
    | null ht hr hc =>
      refine .inr ⟨.plain (.returnCallRef y), trivial, ?_⟩
      exact .returnCallIndirect (.simple (famOf_tableGet x) (tableGet_steps ht hr)
        (.simple (famOf_refCast _) (refCast_steps hc)
          (.returnCallRefNull (ws := W) (c := .plain (.returnCallRef y)) trivial)))

end Silmaril.Wasm.Cfg.Proofs.Region
