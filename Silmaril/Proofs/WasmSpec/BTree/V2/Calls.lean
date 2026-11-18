module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Oba

/-!
# The B-tree library, version 2: calls returning values, `return`, linking

Rules over the `i32` view of `Silmaril.Wasm.Logic.Words` that the B-tree proofs need beyond
those of `Silmaril.Wasm.Logic.Words.Thms`: the total call rule for a call returning one `i32`
(`t_call1`), `return` (`t_ret`) and how a return passes through the postconditions of `if`
arms, `block`/`loop` while loops and function bodies; and how `Resolved` gives the callees
of a module instance.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {rs : List Val}
  {rest : List Admin} {Q : Post H}

/-- **`call x`** of a function with a total specification returning one `i32`, on top of the
stack `rs`. -/
theorem t_call1 {x : FuncIdx} {a : Nat} {fi : FuncInst H} {S : FSpec H} {args : List Val}
    {f : Frame} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → ∃ v : BitVec 32, o = .normal [.i32 v] ∧
      TWP P host s' f (vals (Val.i32 v :: rs).reverse ++ rest) Q) :
    TWP P host s f (vals (rs.reverse ++ args) ++ .plain (.call x) :: rest) Q := by
  refine TSafe.callIdx hx hf hS hpre fun s' o ho => ?_
  rcases ho.2 with ⟨res, rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨b, rfl, hp⟩
  · obtain ⟨v, he, hk⟩ := hpost _ _ hp
    obtain rfl : res = [.i32 v] := by simpa using he
    simpa [seqPostT, TWP] using hk
  · obtain ⟨v, he, -⟩ := hpost _ _ hp
    cases he
  · obtain ⟨v, he, -⟩ := hpost _ _ hp
    cases he

/-- **`return`** with the values `rs` on the stack. -/
theorem t_ret {f : Frame} (h : Q s f (.ret rs.reverse)) :
    TWP P host s f (vals rs.reverse ++ .plain .return_ :: rest) Q :=
  Wp.of_exits (m := .total) (o := .ret rs.reverse) ⟨rest, rfl⟩ h

/-- A return leaves an `if` arm (or a `block`) entered on an empty stack. -/
theorem armPostT_ret {f : Frame} {vs : List Val} (h : Q s f (.ret vs)) :
    armPostT P host [] rest Q s f (.ret vs) := by
  simpa [armPostT, labelPostT, labelPostK, seqPostT] using h

/-- A return leaves a `block (loop …)` while loop. -/
theorem whilePostT_ret {f : Frame} {Inv : Store H → Frame → Prop} {V : Store H → Frame → Nat}
    {v : Nat} {vs : List Val} (h : Q s f (.ret vs)) :
    whilePostT P host Inv V v rest Q s f (.ret vs) := by
  simpa [whilePostT, loopPostT, labelPostT, labelPostK, seqPostT] using h

/-- A function body returning one value `v` by `return` meets the call postcondition
`callPost f vs₀ R` if `R` holds of `[v]`. -/
theorem bodyPostT_ret {f F : Frame} {vs₀ : List Val} {v : Val}
    {R : Store H → Outcome → Prop} (h : R s (.normal [v])) :
    bodyPostT P host 1 f vs₀ (callPost f vs₀ R) s F (.ret [v]) := by
  show labelPostK P host 1 [] [] (framePostT P host 1 f vs₀ (callPost f vs₀ R)) 0 s F (.ret [v])
  simp only [labelPostK, List.nil_append]
  exact ⟨[], [v], rfl, rfl, rfl, .inl ⟨[v], rfl, h⟩⟩

/-- A callee of a module instance whose calls resolve to the module's functions. -/
theorem Resolved.get {s : Store H} {mi : ModuleInst} (h : Resolved s mi) {j : Nat}
    (hj : j < 10) : ∃ (a : Nat) (fi : FuncInst H), mi.funcs[j]? = some a ∧
      s.funcs[a]? = some fi ∧ fi.module = mi ∧ fi.code = .wasm (program.funcs[j]'(by
        have : program.funcs.length = 10 := rfl
        omega)) ∧ HasArity fi (arity j).1 (arity j).2 := by
  obtain ⟨a, fi, h1, h2, h3, ⟨code, hc, hcode⟩, h5⟩ := h j hj
  refine ⟨a, fi, h1, h2, h3, ?_, h5⟩
  have hlt : j < program.funcs.length := by
    have : program.funcs.length = 10 := rfl
    omega
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hc
  rw [hcode, hc]

/-- Only the memories of a store change: the functions are those of the original store. -/
theorem setMem_funcs (s : Store H) (a : Nat) (m : MemInst) : (s.setMem a m).funcs = s.funcs :=
  rfl

/-- `Resolved` depends only on the functions of the store. -/
theorem Resolved.setMem {s : Store H} {mi : ModuleInst} (h : Resolved s mi) (a : Nat)
    (m : MemInst) : Resolved (s.setMem a m) mi := h

end Silmaril.WasmSpec.BTree.V2
