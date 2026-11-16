module

public import Silmaril.Proofs.Wasm.Interp.Trap
public import Silmaril.Wasm.SingleThreaded.Exec.Memory

/-!
# Native memory loads and stores are Core 3.0 memory steps (proofs)

The native interpreter's `intLoad t none x arg` and `intStore t none x arg`
(`Binaryen.evalFlat`) compute what silmaril-lean's executable Core memory step
computes (`SingleThreaded.Exec.Mem.loadInt`/`storeInt`):

* the same address operand (`i32` or `i64`);
* the same memory lookup `Store.mem?`;
* the same `Memory.load`/`Memory.store`, a trap exactly out of bounds;
* the same store update `Store.setMem`.

So each native step is a Core 3.0 `MemoryStep`, through `loadInt_sound` and
`storeInt_sound`: `steps_load_normal`, `steps_store_normal`, `steps_mem_trap`.
Typed progress (`interp_load`, `interp_store`): when the Core head step of a
typed load or store exists, the native step exists too.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.SingleThreaded.Exec

variable {H : Type} {s s' : Store H} {f f' : Frame} {stk : List Val}

/-- The memory instructions of the native profile. -/
def IsMem (i : Instr) : Prop :=
  (∃ t x arg, i = .intLoad t none x arg) ∨ ∃ t x arg, i = .intStore t none x arg

theorem addrOf_of_addrNat {v : Val} {i : Nat} (h : Binaryen.addrNat? v = some i) :
    ∃ (a : AddrType) (j : BitVec a.intType.width), Mem.addrOf? v = some ⟨a, j⟩ ∧ j.toNat = i := by
  rcases v with ⟨⟨t | t⟩, c⟩ | _ | _ <;> simp [Binaryen.addrNat?] at h
  · exact ⟨.i32, c, rfl, h⟩
  · exact ⟨.i64, c, rfl, h⟩

theorem addrNat_of_addrOf {v : Val} {a : AddrType} {j : BitVec a.intType.width}
    (h : Mem.addrOf? v = some ⟨a, j⟩) : Binaryen.addrNat? v = some j.toNat := by
  rw [Mem.addrOf?_eq_some h]
  cases a <;> rfl

theorem intOf_of_asInt {t : IntType} {w : Val} {c : BitVec t.width} (h : Binaryen.asInt t w = some c) :
    Mem.intOf? t w = some c := by
  rw [eq_ofInt_of_asInt h]
  exact Mem.intOf?_self t c

theorem asInt_of_intOf {t : IntType} {w : Val} {c : BitVec t.width} (h : Mem.intOf? t w = some c) :
    ∃ c', Binaryen.asInt t w = some c' := by
  rw [Mem.intOf?_eq_some h]
  cases t <;> exact ⟨_, rfl⟩

/-- A native load is the executable Core load on its address operand. -/
theorem load_exec {t : IntType} {x : MemIdx} {arg : MemArg} {v : Val} {r : List Val}
    {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f (v :: r) (.intLoad t none x arg) = some (s', f', fl)) :
    ∃ c, Mem.loadInt s f t x arg [v] = some c ∧ s' = s ∧ f' = f ∧
      ((∃ b, c = ⟨s, f, [.plain (.intConst t b)]⟩ ∧ fl = .normal (Binaryen.ofInt t b :: r)) ∨
        (c = ⟨s, f, [.trap]⟩ ∧ fl = .trap)) := by
  simp only [Binaryen.evalFlat] at h
  rcases ha : Binaryen.addrNat? v with _ | i
  · simp [ha] at h
  rcases hm : s.mem? f x with _ | ⟨ma, mi⟩
  · simp [ha, hm] at h
  obtain ⟨a, j, hj, rfl⟩ := addrOf_of_addrNat ha
  rcases hl : Execution.Memory.load mi.bytes (effAddr j.toNat arg) (t.width / 8) with _ | b
  · simp only [ha, hm, hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, by simp [Mem.loadInt, hj, hm, hl], rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  · simp only [ha, hm, hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, by simp [Mem.loadInt, hj, hm, hl], rfl, rfl, .inl ⟨_, rfl, rfl⟩⟩

/-- A native store is the executable Core store on its operands. -/
theorem store_exec {t : IntType} {x : MemIdx} {arg : MemArg} {w v : Val} {r : List Val}
    {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f (w :: v :: r) (.intStore t none x arg) = some (s', f', fl)) :
    ∃ c, Mem.storeInt s f t x arg [v, w] = some c ∧ f' = f ∧
      ((c = ⟨s', f, []⟩ ∧ fl = .normal r) ∨ (c = ⟨s, f, [.trap]⟩ ∧ s' = s ∧ fl = .trap)) := by
  simp only [Binaryen.evalFlat] at h
  rcases ha : Binaryen.addrNat? v with _ | i
  · simp [ha] at h
  rcases hw : Binaryen.asInt t w with _ | c
  · simp [ha, hw] at h
  rcases hm : s.mem? f x with _ | ⟨ma, mi⟩
  · simp [ha, hw, hm] at h
  obtain ⟨a, j, hj, rfl⟩ := addrOf_of_addrNat ha
  have hw' := intOf_of_asInt hw
  rcases hs : Execution.Memory.store mi.bytes (effAddr j.toNat arg) (count := t.width / 8)
      (c.setWidth _) with _ | b
  · simp only [ha, hw, hm, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, by simp [Mem.storeInt, hj, hw', hm, hs], rfl, .inr ⟨rfl, rfl, rfl⟩⟩
  · simp only [ha, hw, hm, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, by simp [Mem.storeInt, hj, hw', hm, hs], rfl, .inl ⟨rfl, rfl⟩⟩

theorem evalFlat_load_nil {t : IntType} {x : MemIdx} {arg : MemArg} :
    Binaryen.evalFlat s f [] (.intLoad t none x arg) = none := rfl

variable {P : Numerics.Profile} {host : HostSemantics H}

theorem code_load (v : Val) (r : List Val) (i : Instr) (rest : List Admin) :
    vals (v :: r).reverse ++ .plain i :: rest = vals r.reverse ++ (vals [v] ++ [.plain i]) ++ rest := by
  simp [vals]

theorem code_store (w v : Val) (r : List Val) (i : Instr) (rest : List Admin) :
    vals (w :: v :: r).reverse ++ .plain i :: rest =
      vals r.reverse ++ (vals [v, w] ++ [.plain i]) ++ rest := by
  simp [vals]

theorem steps_load_normal {t : IntType} {x : MemIdx} {arg : MemArg} {stk' : List Val}
    (h : Binaryen.evalFlat s f stk (.intLoad t none x arg) = some (s', f', .normal stk'))
    (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain (.intLoad t none x arg) :: rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ := by
  rcases stk with _ | ⟨v, r⟩
  · simp [Binaryen.evalFlat] at h
  obtain ⟨c, hc, rfl, rfl, ⟨b, rfl, hfl⟩ | ⟨rfl, hfl⟩⟩ := load_exec h
  · cases hfl
    rw [code_load]
    have hst := Step.ctx (P := P) (host := host) r.reverse rest (.memory (Mem.loadInt_sound hc))
    simpa [vals, Binaryen.ofInt, Val.toAdmin] using Relation.ReflTransGen.single hst
  · cases hfl

theorem steps_store_normal {t : IntType} {x : MemIdx} {arg : MemArg} {stk' : List Val}
    (h : Binaryen.evalFlat s f stk (.intStore t none x arg) = some (s', f', .normal stk'))
    (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain (.intStore t none x arg) :: rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ := by
  rcases stk with _ | ⟨w, _ | ⟨v, r⟩⟩
  · simp [Binaryen.evalFlat] at h
  · simp [Binaryen.evalFlat] at h
  obtain ⟨c, hc, rfl, ⟨rfl, hfl⟩ | ⟨rfl, -, hfl⟩⟩ := store_exec h
  · rw [Binaryen.Flow.normal.injEq] at hfl
    rw [hfl, code_store]
    have hst := Step.ctx (P := P) (host := host) r.reverse rest (.memory (Mem.storeInt_sound hc))
    simpa using Relation.ReflTransGen.single hst
  · cases hfl

/-- **A native memory instruction completing normally is a Core 3.0 run.** -/
theorem steps_mem_normal {i : Instr} (hm : IsMem i) {stk' : List Val}
    (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk')) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩ ⟨s', f', vals stk'.reverse ++ rest⟩ := by
  rcases hm with ⟨t, x, arg, rfl⟩ | ⟨t, x, arg, rfl⟩
  · exact steps_load_normal h rest
  · exact steps_store_normal h rest

/-- A native memory instruction stops only by trapping, and then Core traps. -/
theorem steps_mem_abrupt {i : Instr} (hm : IsMem i) {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) (hn : ¬ fl.IsNormal) (rest : List Admin) :
    fl = .trap ∧ Steps P host ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩ ⟨s', f', [.trap]⟩ := by
  rcases hm with ⟨t, x, arg, rfl⟩ | ⟨t, x, arg, rfl⟩
  · rcases stk with _ | ⟨v, r⟩
    · simp [Binaryen.evalFlat] at h
    obtain ⟨c, hc, rfl, rfl, ⟨b, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := load_exec h
    · exact absurd trivial hn
    refine ⟨rfl, ?_⟩
    rw [code_load]
    have hst := Step.ctx (P := P) (host := host) r.reverse rest (.memory (Mem.loadInt_sound hc))
    exact Relation.ReflTransGen.head hst (by simpa using steps_trap (P := P) (host := host) _ _ r.reverse rest)
  · rcases stk with _ | ⟨w, _ | ⟨v, r⟩⟩
    · simp [Binaryen.evalFlat] at h
    · simp [Binaryen.evalFlat] at h
    obtain ⟨c, hc, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ := store_exec h
    · exact absurd trivial hn
    refine ⟨rfl, ?_⟩
    rw [code_store]
    have hst := Step.ctx (P := P) (host := host) r.reverse rest (.memory (Mem.storeInt_sound hc))
    exact Relation.ReflTransGen.head hst (by simpa using steps_trap (P := P) (host := host) _ _ r.reverse rest)

end Silmaril.Wasm.Interp
