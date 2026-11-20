module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Exact.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.GhostRules
public import Silmaril.Semantics.Accept.Mixed.Chunk.Thms
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Proofs: `drainEcho` relates exactly its input bytes to their atom

* **The decoded events of the callouts** and the ghost they move: a drain or a final
  `finish(u, h)` moves the chunk buffer by `chunkStep` (`fin_ghost`); `read(0, 16)` answered
  with `n` appends the `n` bytes at `0` of the memory after the answer (`read_ghost_val`), and
  leaves it on a trap or an exception (`read_ghost_trap`, `read_ghost_throw`); `blob` leaves it
  (`blob_ghost`).
* **The binary drain** (`drain_nil`): five `finish(k, z)` calls, `k = 16, 8, 4, 2, 1`, empty
  every buffer of at most `31` bytes under `chunkStep` (an overrun leaves the buffer).
* **The Hoare-logic proof** (`de_gsat`): `drainEcho z` meets the ghost contract `exactK z sent σ`
  for every writer store `σ`, from the empty buffer, keeping the ghost invariant "the instantiated
  store's shape, at most `16` bytes buffered" (`deInvG`): at every call at most `16` bytes are
  buffered; the drain empties the buffer; `read` fills it with exactly the chunk `c` that `blob`
  then observes (no store between the answer of `read` and the call of `blob`); the answer
  assumption makes the handle `h` of `blob` denote the byte atom of `c` in `σ` (or be the writer's
  sentinel); `finish(|c|, h)` consumes `c`. Every exit (a trap or an exception of any call)
  happens with at most `16` bytes buffered.
* **Every sentinel** (`deOk_all`): the shape `deOk z` holds for every `z`: the shape without the
  body comparison (`deShape_all`) and the instantiated code (`de_code`) are kernel evaluations
  with `z` free (`kernel_rfl`), and the body compares with itself (`ieqs_drainBody`).
* **Exactness** (`exact_of_gsat`): the ghost bridge `tagTraces_gpre` gives, at every `finish(n, h)`
  of a mixed trace, the guarantee in the chunk buffer of the parsing events before it; the
  assume/guarantee law along the chunk buffer
  (`Silmaril.Accept.Mixed.mixedRel_subset_of_chunkAG`) turns it into `memMixedRel … ⊆ exactRel`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.IO
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost
  Silmaril.Wasm.Game.HandleAccept.MemSound.Exact
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)
open Silmaril.Proofs.Wasm.Component.Reference (FuncInst.mapH FuncCode.mapH Config.mapH)

/-! ## Decoded events and the ghost they move -/

/-- The roles. -/
abbrev mR : Roles Unit MixEv Unit Unit := mixRoles {} {}

/-- The imports. -/
abbrev readImp : Import := ⟨"input", "read", .func ⟨0⟩⟩
abbrev blobImp : Import := ⟨"sexp", "blob", .func ⟨0⟩⟩
abbrev finImp : Import := ⟨"input", "finish", .func ⟨1⟩⟩

theorem usedOfI32_small {n : BitVec 32} (h : n.toNat ≤ 16) : usedOfI32 n = some n.toNat := by
  unfold usedOfI32
  have : n.msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, not_le]
    omega
  simp [this]

theorem memWrite_fin (s : Store Nat) (args : List Val) (w : HostReply) :
    memWrite {} (calloutIn finImp (some 0) s args) w = none :=
  memWrite_eq_none (by show ("input", "finish") ≠ ("sexp", "symbol"); decide)
    (by show ("input", "finish") ≠ ("sexp", "string"); decide)
    (by show ("input", "finish") ≠ ("sexp", "blob"); decide)
    (by show ("input", "finish") ≠ ("sexp", "sexp"); decide)

theorem memWrite_read (s : Store Nat) (args : List Val) (w : HostReply) :
    memWrite {} (calloutIn readImp (some 0) s args) w = none :=
  memWrite_eq_none (by show ("input", "read") ≠ ("sexp", "symbol"); decide)
    (by show ("input", "read") ≠ ("sexp", "string"); decide)
    (by show ("input", "read") ≠ ("sexp", "blob"); decide)
    (by show ("input", "read") ≠ ("sexp", "sexp"); decide)

section Ghosts

variable {z : BitVec 32} {sent : Option (BitVec 32)} {σ : Env (BitVec 32) SymStrBytesSExp}

/-- **A `finish(u, h)` call moves the chunk buffer by `chunkStep`**, whatever its answer. -/
theorem fin_ghost (g : List UInt8) (s : Store Nat) {u : BitVec 32} (h : BitVec 32)
    {k : Nat} (hu : usedOfI32 u = some k) (w : HostReply) :
    ansGhost mR (exactK z sent σ) g (calloutIn finImp (some 0) s [.i32 u, .i32 h]) w =
      chunkStep g (.finish k h) := by
  have hc : mixCall {} {} (calloutIn finImp (some 0) s [.i32 u, .i32 h]) =
      some (.p (.finish k h)) := by
    simp [mixCall, memAccept, pullFinish, calloutIn, Val.i32, hu]
  have ha : mixAnswer {} {} (calloutIn finImp (some 0) s [.i32 u, .i32 h]) w = none := by
    unfold mixAnswer
    rw [memWrite_fin]
    simp [pullRead, calloutIn]
  simp only [ansGhost, callGhost, GContract.after, mR, mixRoles, hc, ha, Option.elim]
  rfl

/-- `blob` leaves the chunk buffer. -/
theorem blob_ghost (g : List UInt8) (s : Store Nat) (args : List Val) (w : HostReply) :
    ansGhost mR (exactK z sent σ) g (calloutIn blobImp (some 0) s args) w = g := by
  have hc : mixCall {} {} (calloutIn blobImp (some 0) s args) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  have hr : pullRead {} (calloutIn blobImp (some 0) s args) w = none := by
    simp [pullRead, calloutIn]
  simp only [ansGhost, callGhost, GContract.after, mR, mixRoles, hc, Option.elim, mixAnswer]
  cases hm : memWrite {} (calloutIn blobImp (some 0) s args) w with
  | none => simp [hr]
  | some e => rfl

/-- `read(0, 16)` answered with `n` appends the `n` bytes at `0` of the memory after the
answer. -/
theorem read_ghost_val (g : List UInt8) (s s' : Store Nat) {mi : MemInst}
    (hmi : s'.mems[0]? = some mi) (hsz : 16 ≤ mi.bytes.size) {n : BitVec 32}
    (hn : n.toNat ≤ 16) :
    ansGhost mR (exactK z sent σ) g (calloutIn readImp (some 0) s [.i32 0, .i32 16])
      ⟨.values [.i32 n], memOf (some 0) s'⟩ = g ++ bytesAt mi.bytes ⟨0, n.toNat⟩ := by
  have hc : mixCall {} {} (calloutIn readImp (some 0) s [.i32 0, .i32 16]) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  have hm : memOf (some 0) s' = some mi.bytes := by simp [memOf, hmi]
  have hr : pullRead {} (calloutIn readImp (some 0) s [.i32 0, .i32 16])
      ⟨.values [.i32 n], memOf (some 0) s'⟩ = some (.feed (bytesAt mi.bytes ⟨0, n.toNat⟩)) := by
    simp only [pullRead, calloutIn, Val.i32, replyI32, hm, ↓reduceIte, Option.bind_some]
    unfold segOf
    rw [readBytes_toList (by simp; omega)]
    rfl
  simp only [ansGhost, callGhost, GContract.after, mR, mixRoles, hc, Option.elim, mixAnswer,
    memWrite_read, hr, Option.map_some]
  rfl

/-- `read` answered by a trap leaves the chunk buffer. -/
theorem read_ghost_trap (g : List UInt8) (s : Store Nat) (args : List Val)
    (mem : Option ByteArray) :
    ansGhost mR (exactK z sent σ) g (calloutIn readImp (some 0) s args) ⟨.trap, mem⟩ = g := by
  have hc : mixCall {} {} (calloutIn readImp (some 0) s args) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  simp [ansGhost, callGhost, GContract.after, mR, mixRoles, hc, mixAnswer, memWrite_read,
    pullRead, replyI32]

/-- `read` answered by an exception leaves the chunk buffer. -/
theorem read_ghost_throw (g : List UInt8) (s : Store Nat) (args : List Val) (a : Nat)
    (mem : Option ByteArray) :
    ansGhost mR (exactK z sent σ) g (calloutIn readImp (some 0) s args) ⟨.throw a, mem⟩ = g := by
  have hc : mixCall {} {} (calloutIn readImp (some 0) s args) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  simp [ansGhost, callGhost, GContract.after, mR, mixRoles, hc, mixAnswer, memWrite_read,
    pullRead, replyI32]

end Ghosts

/-! ## The binary drain -/

theorem chunkStep_finish_length (b : List UInt8) (k : Nat) (h : BitVec 32) :
    (chunkStep b (.finish k h)).length = if k ≤ b.length then b.length - k else b.length := by
  unfold chunkStep
  split_ifs with hk <;> simp [hk]

theorem chunkStep_finish_le (b : List UInt8) (k : Nat) (h : BitVec 32) :
    (chunkStep b (.finish k h)).length ≤ b.length := by
  rw [chunkStep_finish_length]
  split_ifs <;> omega

/-- **The binary drain empties every buffer of at most `31` bytes.** -/
theorem drain_nil (z : BitVec 32) (g : List UInt8) (hg : g.length ≤ 31) :
    chunkStep (chunkStep (chunkStep (chunkStep (chunkStep g (.finish 16 z)) (.finish 8 z))
      (.finish 4 z)) (.finish 2 z)) (.finish 1 z) = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp only [chunkStep_finish_length]
  split_ifs <;> omega

/-! ## The instantiated module -/

/-- The default value of the local. -/
def deD : List (Option Val) := [some (.i32 0)]

/-- The shape of the instantiated module, with one memory of one page. -/
def deOk (z : BitVec 32) : Bool :=
  match prep (drainEcho z) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (c.store.mems.map fun mi => mi.bytes.size) == [65536] &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 2 f₂ &&
          fnOk [.i32] (drainBody z) 0 0 [0, 1, 2, 3] [0] deD f₃
       | _ => false)
  | none => false

theorem de_facts {z : BitVec 32} (hz : deOk z = true) {c : Config Nat} {st : Option FuncIdx}
    (hp : prep (drainEcho z) = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [3] ∧
    c.store.mems.length = 1 ∧ (∃ mi, c.store.mems = [mi] ∧ mi.bytes.size = 65536) ∧
    ∃ f₀ f₁ f₂ f₃, c.store.funcs = [f₀, f₁, f₂, f₃] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 2 f₂ = true ∧
      fnOk [.i32] (drainBody z) 0 0 [0, 1, 2, 3] [0] deD f₃ = true := by
  have h := hz
  unfold deOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · rcases hm : c.store.mems with _ | ⟨mi, _ | ⟨mi', ms⟩⟩
    · rw [hm] at h6; cases h6
    · rw [hm] at h6
      exact ⟨mi, rfl, by simpa using h6⟩
    · rw [hm] at h6; simp at h6
  · split at h7
    · rename_i f₀ f₁ f₂ f₃ hf
      simp only [Bool.and_eq_true] at h7
      exact ⟨f₀, f₁, f₂, f₃, hf, h7.1.1.1, h7.1.1.2, h7.1.2, h7.2⟩
    · cases h7

/-! ### Every sentinel

`deOk z` compares the instantiated body with `drainBody z` instruction by instruction
(`ieqs`), which needs the bits of `z`. The rest of the shape, the instantiated code and the
spec instance do not: the kernel evaluates them with `z` free (`kernel_rfl`), since neither
the validator nor the instantiation reads the value of an `i32.const`. -/

/-- `fnOk` without the body comparison. -/
def fnOkNB (locals : List ValType) (np nr : Nat) (funcs mems : List Nat)
    (D : List (Option Val)) (fi : FuncInst Nat) : Bool :=
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == np && rs.length == nr
    | _ => false) &&
  fi.module.funcs == funcs && fi.module.mems == mems &&
  locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) == D

theorem fnOk_of_nb {locals : List ValType} {body : List Instr} {np nr : Nat}
    {funcs mems : List Nat} {D : List (Option Val)} {fi : FuncInst Nat} {ty : TypeIdx}
    (hc : fi.code = .wasm ⟨ty, locals, body⟩) (hb : ieqs body body = true)
    (h : fnOkNB locals np nr funcs mems D fi = true) :
    fnOk locals body np nr funcs mems D fi = true := by
  unfold fnOkNB at h
  unfold fnOk
  rw [hc]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨by simp, hb⟩, h.1.1.1⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- The shape of `deOk z` without the body comparison. -/
def deShape (z : BitVec 32) : Bool :=
  match prep (drainEcho z) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (c.store.mems.map fun mi => mi.bytes.size) == [65536] &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 2 f₂ &&
          fnOkNB [.i32] 0 0 [0, 1, 2, 3] [0] deD f₃
       | _ => false)
  | none => false

/-- **The shape holds for every sentinel** (kernel evaluation with `z` free). -/
theorem deShape_all (z : BitVec 32) : deShape z = true := by
  kernel_rfl

/-- **The instantiated code is `drainBody z`**, for every sentinel. -/
theorem de_code (z : BitVec 32) :
    (prep (drainEcho z)).bind (fun p => p.1.store.funcs[3]?.map FuncInst.code) =
      some (.wasm ⟨⟨2⟩, [.i32], drainBody z⟩) := by
  kernel_rfl

theorem ieqs_drainBody (z : BitVec 32) : ieqs (drainBody z) (drainBody z) = true := by
  simp [drainBody, drainCall, blobEchoBody, ieqs, ieq]

/-- **`deOk z` holds for every sentinel `z`.** -/
theorem deOk_all (z : BitVec 32) : deOk z = true := by
  have h₁ := deShape_all z
  have h₂ := de_code z
  unfold deShape at h₁
  unfold deOk
  generalize prep (drainEcho z) = p at h₁ h₂ ⊢
  rcases p with _ | ⟨c, st⟩
  · cases h₁
  · simp only [Option.bind_some] at h₂
    simp only at h₁ ⊢
    generalize c.store.funcs = fs at h₁ h₂ ⊢
    rcases fs with _ | ⟨f₀, _ | ⟨f₁, _ | ⟨f₂, _ | ⟨f₃, _ | ⟨f₄, fs⟩⟩⟩⟩⟩
    all_goals simp only [Bool.and_false] at h₁
    all_goals try cases h₁
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Option.some.injEq] at h₂
    simp only [Bool.and_eq_true] at h₁ ⊢
    exact ⟨h₁.1, ⟨h₁.2.1, fnOk_of_nb h₂ (ieqs_drainBody z) h₁.2.2⟩⟩

/-- The store invariant: the instantiated functions, one memory of at least `16` bytes. -/
def deInv (z : BitVec 32) (s : Store Nat) : Prop :=
  ∃ c st, prep (drainEcho z) = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1 ∧
    ∃ mi, s.mems[0]? = some mi ∧ 16 ≤ mi.bytes.size

/-- **The ghost invariant**: the store's shape, and at most `16` bytes buffered. -/
def deInvG (z : BitVec 32) (g : List UInt8) (s : Store Nat) : Prop :=
  deInv z s ∧ g.length ≤ 16

/-! ## Observations -/

/-- What `blob(0, n)` observes in a memory of at least `16` bytes, for `n ≤ 16`: the `n` bytes
at `0`. -/
theorem blob_bytes' {s : Store Nat} {mi : MemInst} (hmi : s.mems[0]? = some mi)
    (hsz : 16 ≤ mi.bytes.size) {n : BitVec 32} (hn : n.toNat ≤ 16) :
    (calloutIn blobImp (some 0) s [.i32 0, .i32 n]).bytes32 =
      some (bytesAt mi.bytes ⟨0, n.toNat⟩) := by
  have hm : memOf (some 0) s = some mi.bytes := by simp [memOf, hmi]
  simp only [Callout.bytes32, calloutIn, Callout.args2, Callout.i32?, Val.i32,
    Option.bind_eq_bind, Option.bind_some, Callout.segment, hm]
  exact readBytes_toList (by simp; omega)

/-! ## The Hoare-logic proof -/

section Body

variable {P : Profile} {z : BitVec 32} {sent : Option (BitVec 32)}
  {σ : Env (BitVec 32) SymStrBytesSExp} {f₀ f₁ f₂ : FuncInst Nat} {fs : List (FuncInst Nat)}
  {Inv : List UInt8 → Store Nat → Prop} {Q : Post (Nat × List UInt8)}

/-- The specification host of the module. -/
abbrev deHost (z : BitVec 32) (sent : Option (BitVec 32))
    (σ : Env (BitVec 32) SymStrBytesSExp) : HostSemantics (Nat × List UInt8) :=
  gHost (drainEcho z) (some 0) mR (exactK z sent σ)

/-- **One drain call** `finish(k, z)`: the rest runs with the buffer moved by `chunkStep`. -/
theorem de_drain (h2 : stubOk 2 2 f₂ = true) {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3])
    (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3)
    (hinv : ∀ g sR, sR.funcs = fs → sR.mems.length = 1 → ∀ mi, sR.mems[0]? = some mi →
      16 ≤ mi.bytes.size → g.length ≤ 16 → Inv g sR)
    (hQ : GBodyExits Inv Q) {k : BitVec 32} (hk : k.toNat ≤ 16) {rest : List Instr}
    {g : List UInt8} (hg : g.length ≤ 16) {sR : Store Nat} (hsf : sR.funcs = fs)
    (hml : sR.mems.length = 1) {mi : MemInst} (hmi : sR.mems[0]? = some mi)
    (hsz : 16 ≤ mi.bytes.size)
    (hcont : ∀ sR', sR'.funcs = fs → sR'.mems.length = 1 → ∀ mi', sR'.mems[0]? = some mi' →
      16 ≤ mi'.bytes.size →
      HWP P (deHost z sent σ) (gStore (chunkStep g (.finish k.toNat z)) sR') F
        (vals [] ++ expression rest) Q) :
    HWP P (deHost z sent σ) (gStore g sR) F (vals [] ++ expression (drainCall k z ++ rest)) Q := by
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  show HWP _ _ _ _ (vals [] ++ expression (.intConst .i32 k :: .intConst .i32 z :: .call ⟨2⟩ ::
    rest)) _
  refine GX.i32Const (us := []) ?_
  refine GX.i32Const (us := [] ++ [.i32 k]) ?_
  refine hwp_gcall (us := []) (args := [.i32 k, .i32 z]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := finImp) (g := g) (sR := sR) rfl (by rw [hFf]; rfl) (by rw [hsf, hfs]; rfl) hc₂ he₂
    (by simp [hn₂]) rfl ⟨hg, fun n h hd => ?_⟩ ?_
  · obtain ⟨rfl, rfl⟩ := finish_args hd
    exact .inl rfl
  rintro sR' r ⟨⟨hfs', hml'⟩, hg', hshape⟩ -
  rw [fin_ghost _ _ _ (usedOfI32_small hk)]
  obtain ⟨mi', hmi', hsz'⟩ := hg' mi hmi
  have hfs'' : sR'.funcs = fs := hfs'.trans hsf
  have hml'' : sR'.mems.length = 1 := hml'.trans hml
  have hlen := (chunkStep_finish_le g k.toNat z).trans hg
  have hi' := hinv _ sR' hfs'' hml'' mi' hmi' (by omega) hlen
  refine ⟨fun res hr => ?_, fun _ => (hQ _ _ hi' F).2.2.1, fun a _ => (hQ _ _ hi' F).2.2.2 a⟩
  obtain rfl := (hshape res hr).2.2 rfl
  exact hcont sR' hfs'' hml'' mi' hmi' (by omega)

/-- **The read/blob/finish tail** (the body of `blobEcho`), from the empty buffer. -/
theorem de_tail (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true)
    (h2 : stubOk 2 2 f₂ = true) {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3])
    (hFl : F.locals = deD) (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3)
    (hinv : ∀ g sR, sR.funcs = fs → sR.mems.length = 1 → ∀ mi, sR.mems[0]? = some mi →
      16 ≤ mi.bytes.size → g.length ≤ 16 → Inv g sR)
    (hQ : GBodyExits Inv Q) {sR : Store Nat} (hsf : sR.funcs = fs) (hml : sR.mems.length = 1)
    {mi : MemInst} (hmi : sR.mems[0]? = some mi) (hsz : 16 ≤ mi.bytes.size) :
    HWP P (deHost z sent σ) (gStore [] sR) F (vals [] ++ expression blobEchoBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have hf0 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ := fun s' h => by
    rw [h, hfs]; rfl
  have hf1 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[1]? = some f₁ := fun s' h => by
    rw [h, hfs]; rfl
  have hf2 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[2]? = some f₂ := fun s' h => by
    rw [h, hfs]; rfl
  unfold blobEchoBody
  -- read(0, 16)
  refine GX.i32Const (us := []) ?_
  refine GX.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_gcall (us := []) (args := [.i32 0, .i32 16]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := readImp) (g := []) (sR := sR) rfl (by rw [hFf]; rfl) (hf0 _ hsf) hc₀ he₀
    (by simp [hn₀]) rfl ⟨by simp, fun n h hd => by simp [pullFinish, calloutIn] at hd⟩ ?_
  rintro s₁ r ⟨⟨hfs₁, hml₁⟩, hg₁, hshape⟩ -
  obtain ⟨mi₁, hmi₁, hsz₁⟩ := hg₁ mi hmi
  have hfs₁' : s₁.funcs = fs := hfs₁.trans hsf
  have hml₁' : s₁.mems.length = 1 := hml₁.trans hml
  have hi₀ : Inv [] s₁ := hinv [] s₁ hfs₁' hml₁' mi₁ hmi₁ (by omega) (by simp)
  refine ⟨fun res hr => ?_, fun hr => ?_, fun a hr => ?_⟩
  rotate_left
  · subst hr; rw [read_ghost_trap]; exact (hQ _ _ hi₀ F).2.2.1
  · subst hr; rw [read_ghost_throw]; exact (hQ _ _ hi₀ F).2.2.2 a
  obtain ⟨n, rfl, hn⟩ := (hshape res hr).1 rfl
  subst hr
  have hn16 : n.toNat ≤ 16 := hn 0 16 rfl
  rw [read_ghost_val _ _ _ hmi₁ (by omega) hn16, List.nil_append]
  set c := bytesAt mi₁.bytes ⟨0, n.toNat⟩ with hcdef
  have hcl : c.length = n.toNat := Silmaril.Wasm.Logic.Core.length_bytesAt (by
    simp only [Region.InBounds, Region.stop]; omega)
  have hc16 : c.length ≤ 16 := by omega
  refine GX.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, deD, Idx.toNat]) ?_
  have hv : (F.setLocal ⟨0⟩ (.i32 n)).local? ⟨0⟩ = some (some (.i32 n)) := by
    simp [Frame.local?, Frame.setLocal, hFl, deD, Idx.toNat]
  refine GX.localGet (us := []) hv ?_
  refine GX.i32Const (us := [] ++ [.i32 n]) ?_
  refine GX.localGet (us := [] ++ [.i32 n] ++ [.i32 0]) hv ?_
  -- blob(0, n)
  have hcb := blob_bytes' hmi₁ (by omega) hn16
  show HWP _ _ _ _ (vals ([.i32 n] ++ [.i32 0, .i32 n]) ++ _) _
  refine hwp_gcall (us := [.i32 n]) (args := [.i32 0, .i32 n]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := blobImp) (g := c) (sR := s₁) rfl (by show F.module.funcs[_]? = _; rw [hFf]; rfl)
    (hf1 _ hfs₁') hc₁ he₁ (by simp [hn₁]) rfl
    ⟨hc16, fun n h hd => by simp [pullFinish, calloutIn] at hd⟩ ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hg₂, hshape⟩ hans
  rw [blob_ghost]
  obtain ⟨mi₂, hmi₂, hsz₂⟩ := hg₂ mi₁ hmi₁
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁'
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hml₁'
  have hi₂ : Inv c s₂ := hinv c s₂ hfs₂' hml₂' mi₂ hmi₂ (by omega) hc16
  refine ⟨fun res hr => ?_, fun _ => (hQ _ _ hi₂ _).2.2.1, fun a _ => (hQ _ _ hi₂ _).2.2.2 a⟩
  obtain ⟨h, rfl⟩ := (hshape res hr).2.1 rfl
  subst hr
  have hagree : sent = some h ∨ σ h = some (bytesAtom c) := by
    have hw := mixAnswer_w (memWrite_blob (h := h) (mem := memOf (some 0) s₂) rfl hcb)
    rcases hans _ hw _ _ _ rfl with hs | ⟨t, ht, hσ⟩
    · exact .inl hs
    · simp only [Writer.built, Env.lookupAll, sexpW, List.mapM_nil] at ht
      rw [hσ, ← ht]
      exact .inr rfl
  -- finish(n, h)
  show HWP _ _ _ _ (vals ([] ++ [.i32 n, .i32 h]) ++ _) _
  refine hwp_gcall (us := []) (args := [.i32 n, .i32 h]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := finImp) (g := c) (sR := s₂) rfl (by show F.module.funcs[_]? = _; rw [hFf]; rfl)
    (hf2 _ hfs₂') hc₂ he₂ (by simp [hn₂]) rfl ⟨hc16, fun n' h' hd => ?_⟩ ?_
  · obtain ⟨rfl, rfl⟩ := finish_args hd
    rcases hagree with hs | hσ
    · exact .inr (.inl hs)
    · refine .inr (.inr ⟨by omega, ?_⟩)
      rw [List.take_of_length_le (by omega)]
      exact hσ
  rintro s₃ r ⟨⟨hfs₃, hml₃⟩, hg₃, hshape⟩ -
  rw [fin_ghost _ _ _ (usedOfI32_small hn16)]
  have hnil : chunkStep c (.finish n.toNat h) = [] := by
    simp only [chunkStep, show n.toNat ≤ c.length by omega, ↓reduceIte]
    exact List.drop_eq_nil_of_le (by omega)
  rw [hnil]
  obtain ⟨mi₃, hmi₃, hsz₃⟩ := hg₃ mi₂ hmi₂
  have hi₃ : Inv [] s₃ :=
    hinv [] s₃ (hfs₃.trans hfs₂') (hml₃.trans hml₂') mi₃ hmi₃ (by omega) (by simp)
  refine ⟨fun res hr => ?_, fun _ => (hQ _ _ hi₃ _).2.2.1, fun a _ => (hQ _ _ hi₃ _).2.2.2 a⟩
  obtain rfl := (hshape res hr).2.2 rfl
  exact GX.done (hQ _ _ hi₃ _).1

/-- **The body of `run`**: from any buffer of at most `16` bytes. -/
theorem de_body (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true)
    (h2 : stubOk 2 2 f₂ = true) {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3])
    (hFl : F.locals = deD) (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3)
    (hinv : ∀ g sR, sR.funcs = fs → sR.mems.length = 1 → ∀ mi, sR.mems[0]? = some mi →
      16 ≤ mi.bytes.size → g.length ≤ 16 → Inv g sR)
    (hQ : GBodyExits Inv Q) {g : List UInt8} (hg : g.length ≤ 16) {sR : Store Nat}
    (hsf : sR.funcs = fs) (hml : sR.mems.length = 1) {mi : MemInst}
    (hmi : sR.mems[0]? = some mi) (hsz : 16 ≤ mi.bytes.size) :
    HWP P (deHost z sent σ) (gStore g sR) F (vals [] ++ expression (drainBody z)) Q := by
  have hd := drain_nil z g (by omega)
  unfold drainBody
  simp only [List.append_assoc]
  refine de_drain h2 hFf hfs hinv hQ (k := 16) (by decide) hg hsf hml hmi hsz
    fun s₁ hs₁ hl₁ mi₁ hmi₁ hsz₁ => ?_
  refine de_drain h2 hFf hfs hinv hQ (k := 8) (by decide)
    ((chunkStep_finish_le _ _ _).trans hg) hs₁ hl₁ hmi₁ hsz₁
    fun s₂ hs₂ hl₂ mi₂ hmi₂ hsz₂ => ?_
  refine de_drain h2 hFf hfs hinv hQ (k := 4) (by decide)
    (((chunkStep_finish_le _ _ _).trans (chunkStep_finish_le _ _ _)).trans hg) hs₂ hl₂ hmi₂ hsz₂
    fun s₃ hs₃ hl₃ mi₃ hmi₃ hsz₃ => ?_
  refine de_drain h2 hFf hfs hinv hQ (k := 2) (by decide)
    ((((chunkStep_finish_le _ _ _).trans (chunkStep_finish_le _ _ _)).trans
      (chunkStep_finish_le _ _ _)).trans hg) hs₃ hl₃ hmi₃ hsz₃
    fun s₄ hs₄ hl₄ mi₄ hmi₄ hsz₄ => ?_
  refine de_drain h2 hFf hfs hinv hQ (k := 1) (by decide)
    (((((chunkStep_finish_le _ _ _).trans (chunkStep_finish_le _ _ _)).trans
      (chunkStep_finish_le _ _ _)).trans (chunkStep_finish_le _ _ _)).trans hg) hs₄ hl₄ hmi₄
    hsz₄ fun s₅ hs₅ hl₅ mi₅ hmi₅ hsz₅ => ?_
  have hd' : chunkStep (chunkStep (chunkStep (chunkStep (chunkStep g
      (.finish (16 : BitVec 32).toNat z)) (.finish (8 : BitVec 32).toNat z))
      (.finish (4 : BitVec 32).toNat z)) (.finish (2 : BitVec 32).toNat z))
      (.finish (1 : BitVec 32).toNat z) = [] := hd
  rw [hd']
  exact de_tail h0 h1 h2 hFf hFl hfs hinv hQ hs₅ hl₅ hmi₅ hsz₅

end Body

/-- **`drainEcho z` meets the ghost contract `exactK z sent σ`** from the empty buffer, for every
profile, writer sentinel and writer store, when its instance has the checked shape. -/
theorem de_gsat (P : Profile) {z : BitVec 32} (hz : deOk z = true) (sent : Option (BitVec 32))
    (σ : Env (BitVec 32) SymStrBytesSExp) :
    GMemSat P (drainEcho z) 0 mR (exactK z sent σ) (deInvG z) [] := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, ⟨mi, hmis, hsize⟩, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ :=
    de_facts hz hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  obtain ⟨ps₀, rs₀, hc₀, -, -⟩ := stubOk_spec h0
  have hf0 : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ := fun s h => by
    rw [h, hf]; rfl
  have hinv : ∀ g sR, sR.funcs = c.store.funcs → sR.mems.length = 1 → ∀ mi',
      sR.mems[0]? = some mi' → 16 ≤ mi'.bytes.size → g.length ≤ 16 → deInvG z g sR :=
    fun g sR h h' mi' hm hz' hgl => ⟨⟨c, none, hp, h, h', mi', hm, hz'⟩, hgl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  refine ⟨fun n => Safe.of_exits (o := .normal [])
    (by simp [gConfig, Config.mapH, Config.withStart, hcode]; rfl) ?_, ?_⟩
  · intro vs _ g' sR heq
    obtain ⟨rfl, rfl⟩ := gStore_inj heq (hf0 _ rfl) hc₀
    exact hinv [] _ rfl hml mi hmi (by omega) (by simp)
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 3 := by simpa using ha
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, -, hD⟩ := fnOk_spec h3
  have hfi : ∀ s, deInv z s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine gexport_valid (fi := f₃) (fun g s hs => by rw [hfi s hs.1, hf]; rfl)
    (fun g s hs => ⟨0, 0, f₀, hf0 s (hfi s hs.1), hc₀⟩) hcode3 he hrs ?_
  intro g s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs.1, hf]; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hfs := hfi s hs.1
  obtain ⟨⟨_, _, _, _, hml', mi', hmi', hsz'⟩, hgl⟩ := hs
  exact de_body h0 h1 h2 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hD])
    (fs := c.store.funcs) (by rw [hf]; rfl) hinv hQ hgl hfs hml' hmi' hsz'

/-! ## Exactness -/

/-- The ghost of a tag list is the chunk buffer of its mixed trace's parsing events. -/
theorem tagGhost_mix : ∀ (b : List UInt8) (ts : List (Tag Unit MixEv Unit Unit)),
    tagGhost mixUpd b ts =
      chunkFold b (parseEvents (inputsOf (some (MEv.w WEv.enter)) ts))
  | _, [] => rfl
  | b, .inp (.p e) :: ts => by
      simp only [tagGhost, inputsOf, parseEvents, mixUpd, tagGhost_mix (chunkStep b e) ts]
      rfl
  | b, .inp (.w e) :: ts => by
      simp only [tagGhost, inputsOf, parseEvents, mixUpd, tagGhost_mix b ts]
  | b, .enter _ :: ts => by
      simp only [tagGhost, inputsOf, Option.toList_some, List.singleton_append, parseEvents,
        tagGhost_mix b ts]
  | b, .out _ :: ts => by simp only [tagGhost, inputsOf, tagGhost_mix b ts]
  | b, .exit _ :: ts => by simp only [tagGhost, inputsOf, tagGhost_mix b ts]

section Traces

variable {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {m : Module} {z : BitVec 32}
  {sent : Option (BitVec 32)} {Inv : List UInt8 → Store Nat → Prop}

/-- The ghost bridge read on a mixed trace whose writes agree with `σ`. -/
theorem mix_gpre (hsat : ∀ σ, GMemSat P m 0 mR (exactK z sent σ) Inv [])
    (hE : ∀ s L, Envs s L → ReplyEnvs blobReply s L) {t : List MixEv}
    (ht : t ∈ mixTraces P Envs 0 m {} {}) {σ : Env (BitVec 32) SymStrBytesSExp}
    (hWA : WritesAgree (sexpW MemAtom) sent σ t) {u v : List MixEv} {e : PullEv}
    (hd : t = u ++ .p e :: v) :
    ∃ o, (mixCall {} {} o = some (.p e) ∧
        (exactK z sent σ).pre (chunkFold [] (parseEvents u)) o) ∨
      (∃ w, mixAnswer {} {} o w = some (.p e)) := by
  obtain ⟨ts, hts, rfl⟩ := ht
  obtain ⟨u', v', hd', rfl⟩ := inputsOf_split (e := (MEv.w WEv.enter : MixEv))
    (fun h => by cases h) hd
  have hans : ∀ y, Tag.inp y ∈ u' → (exactK z sent σ).ans y := by
    rintro y hy op args r rfl
    refine hWA op args r ?_
    exact mem_inputsOf_of_inp (by rw [hd']; exact List.mem_append_left _ hy)
  obtain ⟨o, ⟨hc, hpre⟩ | ⟨w, hw, -⟩⟩ := tagTraces_gpre (hsat σ) hE hts hd' hans
  · rw [show (exactK z sent σ).upd = mixUpd from rfl, tagGhost_mix] at hpre
    exact ⟨o, .inl ⟨hc, hpre⟩⟩
  · exact ⟨o, .inr ⟨w, hw⟩⟩

/-- The parsing events of a mixed trace are chunks and finishes. -/
theorem pev_cases (hsat : ∀ σ, GMemSat P m 0 mR (exactK z sent σ) Inv [])
    (hE : ∀ s L, Envs s L → ReplyEnvs blobReply s L) {t : List MixEv}
    (ht : t ∈ mixTraces P Envs 0 m {} {}) {σ : Env (BitVec 32) SymStrBytesSExp}
    (hWA : WritesAgree (sexpW MemAtom) sent σ t) {u v : List MixEv} {e : PullEv}
    (hd : t = u ++ .p e :: v) : (∃ n h, e = .finish n h) ∨ (∃ c, e = .feed c) := by
  obtain ⟨o, ⟨hc, -⟩ | ⟨w, hw⟩⟩ := mix_gpre hsat hE ht hWA hd
  · exact .inl (pullFinish_finish (mixCall_p hc))
  · exact .inr (pullRead_feed (mixAnswer_p hw))

/-- **The guarantee at every `finish` of a mixed trace**, read in the chunk buffer of the parsing
events before it, for every writer store the trace's writes agree with: at most `16` bytes are
buffered, and the handle is a sentinel or denotes the byte atom of the `n` bytes it consumes. -/
theorem finish_guarantee (hsat : ∀ σ, GMemSat P m 0 mR (exactK z sent σ) Inv [])
    (hE : ∀ s L, Envs s L → ReplyEnvs blobReply s L) {t : List MixEv}
    (ht : t ∈ mixTraces P Envs 0 m {} {}) {σ : Env (BitVec 32) SymStrBytesSExp}
    (hWA : WritesAgree (sexpW MemAtom) sent σ t) {u v : List MixEv} {n : Nat} {h : BitVec 32}
    (hd : t = u ++ .p (.finish n h) :: v) :
    (chunkFold [] (parseEvents u)).length ≤ 16 ∧
      (h = z ∨ sent = some h ∨ (n ≤ (chunkFold [] (parseEvents u)).length ∧
        σ h = some (bytesAtom ((chunkFold [] (parseEvents u)).take n)))) := by
  obtain ⟨o, ⟨hc, hpre⟩ | ⟨w, hw⟩⟩ := mix_gpre hsat hE ht hWA hd
  · exact ⟨hpre.1, hpre.2 n h (mixCall_p hc)⟩
  · obtain ⟨c, hc⟩ := pullRead_feed (mixAnswer_p hw)
    cases hc

end Traces

/-- **Exactness from the ghost obligation**: every pair is a byte string related to its byte
atom. -/
theorem exact_of_gsat {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {m : Module}
    {z : BitVec 32} {Inv : List UInt8 → Store Nat → Prop} {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)}
    (hsat : ∀ σ, GMemSat P m 0 mR (exactK z pol.sentinel σ) Inv [])
    (hE : ∀ s L, Envs s L → ReplyEnvs blobReply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    (hz : ppol.sentinel = z) (hs : pol.sentinel = none ∨ pol.sentinel = some ppol.sentinel) :
    memMixedRel P Envs 0 m {} {} pol ppol ⊆ exactRel := by
  refine mixedRel_subset_of_chunkAG hw ha hb ho ?_
  intro t ht σ hWA u e v hd ps w h ps' hps hR hne x hx
  rcases pev_cases hsat hE ht hWA hd with ⟨n, h₀, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨hn, rfl, rfl, -⟩ := hR
    obtain ⟨-, hg⟩ := finish_guarantee hsat hE ht hWA hd
    rw [← hps] at hg
    rcases hg with rfl | hsent | ⟨-, hσ⟩
    · exact absurd hz.symm hne
    · rcases hs with hs | hs
      · rw [hs] at hsent; cases hsent
      · rw [hs] at hsent; exact absurd (Option.some.inj hsent).symm hne
    · rw [hσ] at hx
      cases hx
      rfl
  · exact hR.elim

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact
