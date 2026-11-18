module

public import Silmaril.Sim.X86Real.Defs
public import Silmaril.Wasm.Logic.VCTotal.Thms

/-!
# Verifying functions of the quoted x86 simulators: the generic rule

`tfspec_of_wpc`: a loop-free body whose verification condition (`wpc`, over a totally correct
spec context for its calls) establishes `fnPost` (falling through or `return`) meets a total
function specification. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86Real

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC

variable {H : Type} {P : Profile} {host : HostSemantics H}

@[simp] theorem numI32_inj {a b : BitVec 32} :
    ((⟨.int .i32, a⟩ : NumVal) = ⟨.int .i32, b⟩) ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; rfl⟩

@[simp] theorem numI64_inj {a b : BitVec 64} :
    ((⟨.int .i64, a⟩ : NumVal) = ⟨.int .i64, b⟩) ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; rfl⟩

/-! ## Integer operators (definitional) -/

section
variable {x y : BitVec 32}
@[simp] theorem ib_add32 : intBinOp .i32 .add x y = .ok (x + y) := rfl
@[simp] theorem ib_sub32 : intBinOp .i32 .sub x y = .ok (x - y) := rfl
@[simp] theorem ib_mul32 : intBinOp .i32 .mul x y = .ok (x * y) := rfl
@[simp] theorem ib_and32 : intBinOp .i32 .and x y = .ok (x &&& y) := rfl
@[simp] theorem ib_or32 : intBinOp .i32 .or x y = .ok (x ||| y) := rfl
@[simp] theorem ib_xor32 : intBinOp .i32 .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem ib_shl32 : intBinOp .i32 .shl x y = .ok (x <<< (y.toNat % 32)) := rfl
@[simp] theorem ib_shru32 : intBinOp .i32 (.shr .unsigned) x y = .ok (x >>> (y.toNat % 32)) := rfl
end

section
variable {x y : BitVec 64}
@[simp] theorem ib_add64 : intBinOp .i64 .add x y = .ok (x + y) := rfl
@[simp] theorem ib_sub64 : intBinOp .i64 .sub x y = .ok (x - y) := rfl
@[simp] theorem ib_mul64 : intBinOp .i64 .mul x y = .ok (x * y) := rfl
@[simp] theorem ib_and64 : intBinOp .i64 .and x y = .ok (x &&& y) := rfl
@[simp] theorem ib_or64 : intBinOp .i64 .or x y = .ok (x ||| y) := rfl
@[simp] theorem ib_xor64 : intBinOp .i64 .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem ib_shl64 : intBinOp .i64 .shl x y = .ok (x <<< (y.toNat % 64)) := rfl
@[simp] theorem ib_shru64 : intBinOp .i64 (.shr .unsigned) x y = .ok (x >>> (y.toNat % 64)) := rfl
@[simp] theorem ib_shrs64 : intBinOp .i64 (.shr .signed) x y = .ok (x.sshiftRight (y.toNat % 64)) :=
  rfl
end

section
variable {t : IntType} {x y : BitVec t.width}
@[simp] theorem ib_add : intBinOp t .add x y = .ok (x + y) := rfl
@[simp] theorem ib_sub : intBinOp t .sub x y = .ok (x - y) := rfl
@[simp] theorem ib_and : intBinOp t .and x y = .ok (x &&& y) := rfl
@[simp] theorem ib_or : intBinOp t .or x y = .ok (x ||| y) := rfl
@[simp] theorem ib_xor : intBinOp t .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem ib_shl : intBinOp t .shl x y = .ok (x <<< (y.toNat % t.width)) := rfl
@[simp] theorem ib_shru : intBinOp t (.shr .unsigned) x y = .ok (x >>> (y.toNat % t.width)) := rfl
@[simp] theorem iu_popcnt : intUnOp t .popcnt x = x.cpop := rfl
end

@[simp] theorem and_ones64 (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 by decide]; exact BitVec.and_allOnes

theorem lt_of_getElem?_some {α : Type} {l : List α} {n : Nat} {a : α} (h : l[n]? = some a) :
    n < l.length := (List.getElem?_eq_some_iff.1 h).1

theorem getElem_of_getElem?_some {α : Type} {l : List α} {n : Nat} {a : α} (h : l[n]? = some a)
    (hn : n < l.length) : l[n] = a := by
  rw [List.getElem?_eq_getElem hn] at h; exact Option.some.inj h

/-! ## Tests and comparisons as `if` (stated at `BitVec n`, avoiding `IntValue` widths) -/

@[simp] theorem eqz64 (r : BitVec 64) :
    intTestOp .i64 .eqz r = if r = 0#64 then 1#32 else 0#32 := by
  show (if (r == 0#64) = true then 1#32 else 0#32) = _; simp

@[simp] theorem eqz32 (r : BitVec 32) :
    intTestOp .i32 .eqz r = if r = 0#32 then 1#32 else 0#32 := by
  show (if (r == 0#32) = true then 1#32 else 0#32) = _; simp

@[simp] theorem ne64 (x y : BitVec 64) :
    intRelOp .i64 .ne x y = if x = y then 0#32 else 1#32 := by
  show (if (x != y) = true then 1#32 else 0#32) = _; by_cases h : x = y <;> simp [h]

@[simp] theorem eq32 (x y : BitVec 32) :
    intRelOp .i32 .eq x y = if x = y then 1#32 else 0#32 := by
  show (if (x == y) = true then 1#32 else 0#32) = _; simp

@[simp] theorem ltu64 (x y : BitVec 64) :
    intRelOp .i64 (.lt .unsigned) x y = if x.toNat < y.toNat then 1#32 else 0#32 := by
  show (if decide (x.toNat < y.toNat) = true then 1#32 else 0#32) = _; simp

@[simp] theorem ltu32 (x y : BitVec 32) :
    intRelOp .i32 (.lt .unsigned) x y = if x.toNat < y.toNat then 1#32 else 0#32 := by
  show (if decide (x.toNat < y.toNat) = true then 1#32 else 0#32) = _; simp

@[simp] theorem geu32 (x y : BitVec 32) :
    intRelOp .i32 (.ge .unsigned) x y = if x.toNat ≥ y.toNat then 1#32 else 0#32 := by
  show (if decide (x.toNat ≥ y.toNat) = true then 1#32 else 0#32) = _; simp

theorem tfspec_of_wpc [Γ : VCSpecs H] (hΓ : Γ.TValid P host) {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    {S : Silmaril.Wasm.Logic.Hoare.FSpec H} (hl : loops code.body = 0)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpc (fun _ _ _ _ => True) 0 code.body
      (fnPost rs.length (S.post s args)) s (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a S :=
  TFSpecAt.of_fnPost hfi hcode he hlen fun s args hp => by
    have h := wpc_sound_total_ctx hΓ (fun _ _ _ _ => True) 0 _ hl _ _ _ [] (hvc s args hp)
    simpa [vals] using h

end Silmaril.Sim.X86Real
