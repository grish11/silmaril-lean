module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Machine
public import Silmaril.Wasm.Examples.Common.Thms

@[expose] public section

/-!
# The Farkas checker: evaluating the straight-line code

`exec` (the evaluator of `Silmaril.Wasm.Logic.Core`) on the straight-line parts of the bodies,
from a store holding a machine state (`withMach s₀ m`; the `…X` forms in every fixture,
`withMachX X s₀ m` with frames of `X.mi`, `Fix.Ok`):

* `exec_row`: `row(y, b)` leaves `rowM m y b`;
* `exec_entry`: `entry(j, a)` leaves `entryM m j a` (the load and the store of the slot are
  `exec1_load`, `exec1_store`; the rest is evaluated by `rfl`);
* the segments of `check` (`exec_test`, `exec_scan`, `exec_tail`).

Evaluation by `rfl` (definitional unfolding) is used instead of `simp` because `simp` leaves
terms that are only type-correct up to unfolding `IntType.width`, which blocks further
rewriting.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 exec_append exec_cons_of_some)

theorem setWidth64 (c : BitVec 64) : BitVec.setWidth IntType.i64.width c = c := BitVec.setWidth_eq c

theorem setWidth64' (c : BitVec 64) : BitVec.setWidth (8 * (IntType.i64.width / 8)) c = c :=
  BitVec.setWidth_eq c

variable {s₀ : Store Nat} {m : Mach} {rs : List Val} {A : BitVec 32}
  {k : Nat}

theorem effAddr_ma8 (n : Nat) : effAddr n ma8 = n := rfl

variable {X : Fix}

/-- Loading slot `k` from the address `A = 8 k`, in a fixture. -/
theorem exec1_loadX (hX : X.Ok) (hA : A.toNat = 8 * k) (hB : m.mem.size = 65536) (hk : k < nVars)
    {F : Frame} (hF : F.module = X.mi) :
    exec1 (withMachX X s₀ m) F (Val.i32 A :: rs) (.intLoad .i64 none ⟨0⟩ ma8) =
      some (withMachX X s₀ m, F, Val.i64 (slot m.mem k) :: rs) := by
  obtain ⟨ls, mi⟩ := F
  subst hF
  obtain ⟨gs, ms, he⟩ := hX.eta
  have hl : Memory.load m.mem (effAddr A.toNat ma8) (IntType.i64.width / 8) = some (slot m.mem k) := by
    rw [effAddr_ma8, hA]
    exact load_slot hB hk
  rw [he]
  show Option.map _ (Memory.load m.mem (effAddr A.toNat ma8) (IntType.i64.width / 8)) = _
  rw [hl]
  exact congrArg (fun c : BitVec 64 => some (withMachX X s₀ m,
    (⟨ls, { X.mi with globals := 0 :: 1 :: 2 :: 3 :: gs, mems := 0 :: ms }⟩ : Frame),
      Val.i64 c :: rs)) (setWidth64 (slot m.mem k))

/-- Storing `w` in slot `k` at the address `A = 8 k`, in a fixture. -/
theorem exec1_storeX (hX : X.Ok) {w : BitVec 64} (hA : A.toNat = 8 * k) (hB : m.mem.size = 65536)
    (hk : k < nVars) {F : Frame} (hF : F.module = X.mi) :
    exec1 (withMachX X s₀ m) F (Val.i64 w :: Val.i32 A :: rs) (.intStore .i64 none ⟨0⟩ ma8) =
      some (withMachX X s₀ { m with mem := setSlot m.mem k w }, F, rs) := by
  obtain ⟨ls, mi⟩ := F
  subst hF
  obtain ⟨gs, ms, he⟩ := hX.eta
  have hs : Memory.store m.mem (effAddr A.toNat ma8) (count := IntType.i64.width / 8)
      (BitVec.setWidth _ w) = some (setSlot m.mem k w) := by
    rw [effAddr_ma8, hA, setWidth64']
    exact store_slot hB hk w
  rw [he]
  show Option.map _ (Memory.store m.mem (effAddr A.toNat ma8) (count := IntType.i64.width / 8)
    (BitVec.setWidth _ w)) = _
  rw [hs]
  rfl

/-- Loading slot `k` from the address `A = 8 k`. -/
theorem exec1_load (hA : A.toNat = 8 * k) (hB : m.mem.size = 65536) (hk : k < nVars) {F : Frame}
    (hF : F.module = farkasMI) :
    exec1 (withMach s₀ m) F (Val.i32 A :: rs) (.intLoad .i64 none ⟨0⟩ ma8) =
      some (withMach s₀ m, F, Val.i64 (slot m.mem k) :: rs) := by
  have h := exec1_loadX (X := Fix.base) (s₀ := s₀) (rs := rs) Fix.base_ok hA hB hk hF
  rwa [withMachX_base] at h

/-- Storing `w` in slot `k` at the address `A = 8 k`. -/
theorem exec1_store {w : BitVec 64} (hA : A.toNat = 8 * k) (hB : m.mem.size = 65536)
    (hk : k < nVars) {F : Frame} (hF : F.module = farkasMI) :
    exec1 (withMach s₀ m) F (Val.i64 w :: Val.i32 A :: rs) (.intStore .i64 none ⟨0⟩ ma8) =
      some (withMach s₀ { m with mem := setSlot m.mem k w }, F, rs) := by
  have h := exec1_storeX (X := Fix.base) (s₀ := s₀) (rs := rs) (w := w) Fix.base_ok hA hB hk hF
  rwa [withMachX_base, withMachX_base] at h

/-! ## `row` -/

/-- The frame of `row(y, b)`. -/
theorem frame_row (y b : BitVec 64) :
    Frame.forCall farkasMI [.i64 y, .i64 b] [.i64] = ⟨[some (.i64 y), some (.i64 b), some (.i64 0)], farkasMI⟩ :=
  rfl

theorem exec_rowX (hX : X.Ok) (y b : BitVec 64) :
    exec (withMachX X s₀ m) ⟨[some (.i64 y), some (.i64 b), some (.i64 0)], X.mi⟩ [] rowBody =
      some (withMachX X s₀ (rowM m y b),
        ⟨[some (.i64 y), some (.i64 b), some (.i64 (m.vb + y * b))], X.mi⟩, []) := by
  obtain ⟨gs, ms, he⟩ := hX.eta
  rw [he]
  rfl

theorem exec_row (y b : BitVec 64) :
    exec (withMach s₀ m) ⟨[some (.i64 y), some (.i64 b), some (.i64 0)], farkasMI⟩ [] rowBody =
      some (withMach s₀ (rowM m y b),
        ⟨[some (.i64 y), some (.i64 b), some (.i64 (m.vb + y * b))], farkasMI⟩, []) :=
  rfl

/-! ## `entry` -/

/-- The frame of `entry(j, a)`. -/
theorem frame_entry (j : BitVec 32) (a : BitVec 64) :
    Frame.forCall farkasMI [.i32 j, .i64 a] [.i32, .i64] =
      ⟨[some (.i32 j), some (.i64 a), some (.i32 0), some (.i64 0)], farkasMI⟩ :=
  rfl

/-- The masked byte address of `entry`. -/
abbrev entryAddr (j : BitVec 32) : BitVec 32 := (j &&& BitVec.ofNat 32 (nVars - 1)) <<< (3 : Nat)

/-- The flag after the checks on the arguments of `entry`. -/
abbrev entryBad (m : Mach) (j : BitVec 32) (a : BitVec 64) : BitVec 32 :=
  m.bad ||| intTestOp .i32 .eqz m.hr ||| intRelOp .i32 (.ge .unsigned) j (BitVec.ofNat 32 nVars) |||
    ltS a (-cB) ||| gtS a cB

/-- The code of `entry` before the load. -/
def entryA : List Instr :=
  [.globalGet ⟨0⟩, .globalGet ⟨1⟩, .intTestOp .i32 .eqz, .intBinOp .i32 .or,
   .localGet ⟨0⟩, i32c nVars, .intRelOp .i32 (.ge .unsigned), .intBinOp .i32 .or] ++
  orOut ⟨1⟩ (-cB) cB ++
  [.localGet ⟨0⟩, i32c (nVars - 1), .intBinOp .i32 .and, i32c 3, .intBinOp .i32 .shl,
   .localSet ⟨2⟩, .localGet ⟨2⟩, .localGet ⟨2⟩]

/-- The code of `entry` between the load and the store. -/
def entryB : List Instr :=
  [.globalGet ⟨2⟩, .localGet ⟨1⟩, .intBinOp .i64 .mul, .intBinOp .i64 .add, .localSet ⟨3⟩,
   .localGet ⟨3⟩]

/-- The code of `entry` after the store. -/
def entryC : List Instr := orOut ⟨3⟩ (-aB) aB ++ [.globalSet ⟨0⟩]

theorem entryBody_eq : entryBody =
    entryA ++ .intLoad .i64 none ⟨0⟩ ma8 :: (entryB ++ .intStore .i64 none ⟨0⟩ ma8 :: entryC) := rfl

theorem exec_entryX (hX : X.Ok) (hB : m.mem.size = 65536) (j : BitVec 32) (a : BitVec 64) :
    exec (withMachX X s₀ m) ⟨[some (.i32 j), some (.i64 a), some (.i32 0), some (.i64 0)], X.mi⟩ []
        entryBody =
      some (withMachX X s₀ (entryM m j a),
        ⟨[some (.i32 j), some (.i64 a), some (.i32 (entryAddr j)),
          some (.i64 (slot m.mem (j.toNat % nVars) + m.y * a))], X.mi⟩, []) := by
  have hk : j.toNat % nVars < nVars := Nat.mod_lt _ (by decide)
  have hA : (entryAddr j).toNat = 8 * (j.toNat % nVars) := addr_mask j
  let t := slot m.mem (j.toNat % nVars) + m.y * a
  let F₁ : Frame := ⟨[some (.i32 j), some (.i64 a), some (.i32 (entryAddr j)), some (.i64 0)], X.mi⟩
  let F₂ : Frame := ⟨[some (.i32 j), some (.i64 a), some (.i32 (entryAddr j)), some (.i64 t)], X.mi⟩
  obtain ⟨gs, ms, he⟩ := hX.eta
  have hA' : exec (withMachX X s₀ m) ⟨[some (.i32 j), some (.i64 a), some (.i32 0), some (.i64 0)], X.mi⟩
      [] entryA = some (withMachX X s₀ m, F₁, [.i32 (entryAddr j), .i32 (entryAddr j),
        .i32 (entryBad m j a)]) := by
    simp only [F₁]
    rw [he]
    rfl
  have hL := exec1_loadX (s₀ := s₀) (rs := [.i32 (entryAddr j), .i32 (entryBad m j a)])
    hX hA hB hk (F := F₁) rfl
  have hB' : exec (withMachX X s₀ m) F₁ [.i64 (slot m.mem (j.toNat % nVars)), .i32 (entryAddr j),
      .i32 (entryBad m j a)] entryB =
        some (withMachX X s₀ m, F₂, [.i64 t, .i32 (entryAddr j), .i32 (entryBad m j a)]) := by
    simp only [F₁, F₂]
    rw [he]
    rfl
  have hS := exec1_storeX (s₀ := s₀) (rs := [.i32 (entryBad m j a)]) (w := t) hX hA hB hk
    (F := F₂) rfl
  have hC : exec (withMachX X s₀ { m with mem := setSlot m.mem (j.toNat % nVars) t }) F₂
      [.i32 (entryBad m j a)] entryC = some (withMachX X s₀ (entryM m j a), F₂, []) := by
    simp only [F₂]
    rw [he]
    rfl
  rw [entryBody_eq, exec_append, hA']
  dsimp only
  rw [exec_cons_of_some hL, exec_append, hB']
  dsimp only
  rw [exec_cons_of_some hS, hC]

theorem exec_entry (hB : m.mem.size = 65536) (j : BitVec 32) (a : BitVec 64) :
    exec (withMach s₀ m) ⟨[some (.i32 j), some (.i64 a), some (.i32 0), some (.i64 0)], farkasMI⟩ []
        entryBody =
      some (withMach s₀ (entryM m j a),
        ⟨[some (.i32 j), some (.i64 a), some (.i32 (entryAddr j)),
          some (.i64 (slot m.mem (j.toNat % nVars) + m.y * a))], farkasMI⟩, []) := by
  have h := exec_entryX (X := Fix.base) (s₀ := s₀) Fix.base_ok hB j a
  rwa [withMachX_base, withMachX_base] at h

/-! ## `check` -/

/-- The loop test of `check`. -/
def loopTest : List Instr := [.localGet ⟨0⟩, i32c nVars, .intRelOp .i32 (.ge .unsigned)]

/-- The scan step of `check` before the load. -/
def scanA : List Instr := [.localGet ⟨1⟩, .localGet ⟨0⟩, i32c 3, .intBinOp .i32 .shl]

/-- The scan step of `check` between the load and the store. -/
def scanB : List Instr :=
  [i64c 0, .intRelOp .i64 .ne, .intBinOp .i32 .or, .localSet ⟨1⟩, .localGet ⟨0⟩, i32c 3,
   .intBinOp .i32 .shl, i64c 0]

/-- The scan step of `check` after the store. -/
def scanC : List Instr := [.localGet ⟨0⟩, i32c 1, .intBinOp .i32 .add, .localSet ⟨0⟩]

/-- One scan step: `nz |= acc[i] ≠ 0; acc[i] := 0; i += 1`. -/
def scan : List Instr :=
  scanA ++ .intLoad .i64 none ⟨0⟩ ma8 :: (scanB ++ .intStore .i64 none ⟨0⟩ ma8 :: scanC)

/-- The code after the loop. -/
def checkTail : List Instr :=
  [.globalGet ⟨0⟩, .intTestOp .i32 .eqz, .localGet ⟨1⟩, .intTestOp .i32 .eqz, .intBinOp .i32 .and,
   .globalGet ⟨3⟩, i64c 0, .intRelOp .i64 (.lt .signed), .intBinOp .i32 .and,
   i32c 0, .globalSet ⟨0⟩, i32c 0, .globalSet ⟨1⟩, i64c 0, .globalSet ⟨2⟩, i64c 0, .globalSet ⟨3⟩]

theorem loopBody_eq : loopBody = loopTest ++ .brIf ⟨1⟩ :: (scan ++ [.br ⟨0⟩]) := rfl

theorem checkBody_eq : checkBody = .block .empty [.loop .empty loopBody] :: checkTail := rfl

/-- The frame of the scan loop, in the module instance `mi`. -/
abbrev scanFrameX (mi : ModuleInst) (i nz : BitVec 32) : Frame := ⟨[some (.i32 i), some (.i32 nz)], mi⟩

/-- The frame of the scan loop. -/
abbrev scanFrame (i nz : BitVec 32) : Frame := scanFrameX farkasMI i nz

/-- The frame of `check()`. -/
theorem frame_check : Frame.forCall farkasMI [] [.i32, .i32] = scanFrame 0 0 := rfl

theorem frame_checkX (mi : ModuleInst) : Frame.forCall mi [] [.i32, .i32] = scanFrameX mi 0 0 := rfl

theorem exec_testX (mi : ModuleInst) (s : Store Nat) (i nz : BitVec 32) :
    exec s (scanFrameX mi i nz) [] loopTest =
      some (s, scanFrameX mi i nz, [.i32 (intRelOp .i32 (.ge .unsigned) i (BitVec.ofNat 32 nVars))]) :=
  rfl

theorem exec_test (s : Store Nat) (i nz : BitVec 32) :
    exec s (scanFrame i nz) [] loopTest =
      some (s, scanFrame i nz, [.i32 (intRelOp .i32 (.ge .unsigned) i (BitVec.ofNat 32 nVars))]) :=
  rfl

/-- The address of slot `i`. -/
abbrev scanAddr (i : BitVec 32) : BitVec 32 := i <<< (3 : Nat)

theorem scanAddr_toNat {i : BitVec 32} (hi : i.toNat < nVars) : (scanAddr i).toNat = 8 * i.toNat := by
  have hi' : i.toNat < 8192 := hi
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The flag after scanning slot `i`. -/
abbrev scanNz (B : ByteArray) (i nz : BitVec 32) : BitVec 32 :=
  nz ||| intRelOp .i64 .ne (slot B i.toNat) (BitVec.ofInt 64 0)

theorem exec_scanX (hX : X.Ok) (hB : m.mem.size = 65536) {i nz : BitVec 32} (hi : i.toNat < nVars) :
    exec (withMachX X s₀ m) (scanFrameX X.mi i nz) [] scan =
      some (withMachX X s₀ { m with mem := setSlot m.mem i.toNat 0 },
        scanFrameX X.mi (i + 1) (scanNz m.mem i nz), []) := by
  have hA := scanAddr_toNat hi
  let F₁ : Frame := ⟨[some (.i32 i), some (.i32 (scanNz m.mem i nz))], X.mi⟩
  have hA' : exec (withMachX X s₀ m) (scanFrameX X.mi i nz) [] scanA =
      some (withMachX X s₀ m, scanFrameX X.mi i nz, [.i32 (scanAddr i), .i32 nz]) := rfl
  have hL := exec1_loadX (s₀ := s₀) (rs := [.i32 nz]) hX hA hB hi (F := scanFrameX X.mi i nz) rfl
  have hB' : exec (withMachX X s₀ m) (scanFrameX X.mi i nz) [.i64 (slot m.mem i.toNat), .i32 nz] scanB =
      some (withMachX X s₀ m, F₁, [.i64 (BitVec.ofInt 64 0), .i32 (scanAddr i)]) := rfl
  have hS := exec1_storeX (s₀ := s₀) (rs := []) (w := BitVec.ofInt 64 0) hX hA hB hi (F := F₁) rfl
  have hC : exec (withMachX X s₀ { m with mem := setSlot m.mem i.toNat (BitVec.ofInt 64 0) }) F₁ []
      scanC = some (withMachX X s₀ { m with mem := setSlot m.mem i.toNat 0 },
        scanFrameX X.mi (i + 1) (scanNz m.mem i nz), []) :=
    rfl
  rw [scan, exec_append, hA']
  dsimp only
  rw [exec_cons_of_some hL, exec_append, hB']
  dsimp only
  rw [exec_cons_of_some hS, hC]

theorem exec_scan (hB : m.mem.size = 65536) {i nz : BitVec 32} (hi : i.toNat < nVars) :
    exec (withMach s₀ m) (scanFrame i nz) [] scan =
      some (withMach s₀ { m with mem := setSlot m.mem i.toNat 0 },
        scanFrame (i + 1) (scanNz m.mem i nz), []) := by
  have h := exec_scanX (X := Fix.base) (s₀ := s₀) Fix.base_ok hB (nz := nz) hi
  rwa [withMachX_base, withMachX_base] at h

/-- The machine state after `check`: everything reset, the memory as the scan left it. -/
def checkEnd (B : ByteArray) : Mach := ⟨0, 0, 0, 0, B⟩

/-- The result of `check`: `bad = 0 ∧ nz = 0 ∧ accB < 0`. -/
abbrev checkRes (m : Mach) (nz : BitVec 32) : BitVec 32 :=
  intTestOp .i32 .eqz m.bad &&& intTestOp .i32 .eqz nz &&& ltS m.vb 0

theorem exec_tailX (hX : X.Ok) (i nz : BitVec 32) :
    exec (withMachX X s₀ m) (scanFrameX X.mi i nz) [] checkTail =
      some (withMachX X s₀ (checkEnd m.mem), scanFrameX X.mi i nz, [.i32 (checkRes m nz)]) := by
  obtain ⟨gs, ms, he⟩ := hX.eta
  rw [he]
  rfl

theorem exec_tail (i nz : BitVec 32) :
    exec (withMach s₀ m) (scanFrame i nz) [] checkTail =
      some (withMach s₀ (checkEnd m.mem), scanFrame i nz, [.i32 (checkRes m nz)]) :=
  rfl

end Silmaril.Wasm.Examples.Farkas
