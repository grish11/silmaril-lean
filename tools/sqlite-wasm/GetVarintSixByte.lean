module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties
import SqliteWasm.VarintContinuation
import Silmaril.Wasm.Auto2.VCGen.Thms
import Silmaril.Wasm.Logic.Memory.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

open Silmaril.Wasm.Auto2.VCGen

namespace SixByteReader

private def quoted : Func := (definedFunction? sqlite 434).get (by kernel_rfl)

private theorem quotedSelected : definedFunction? sqlite 434 = some quoted := by kernel_rfl

private def contract (width : Nat) : FnSpec :=
  { params := [.i32, .i32]
    results := [.i32]
    mem := true
    total := true
    pre := .pr 0 (.v 0) [.var .i32 0, .var .i32 1]
    post := .and (.rel .eq (.loc .i32 0) (.lit .i32 width))
      (.pr2 0 (.v 0) .cur [.var .i32 0, .var .i32 1]) }

open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)

private theorem reachesResult {H : Type} {P : Profile} {host : HostSemantics H}
    {start : Config H} {store : Store H} {caller : Frame} {result : List Val}
    (safe : TSafe P host (fun s f o => s = store ∧ f = caller ∧ o = .normal result) start) :
    Steps P host start ⟨store, caller, vals result⟩ := by
  induction safe with
  | @exit c outcome exits post =>
    rcases c with ⟨before, frame, code⟩
    obtain ⟨rfl, rfl, rfl⟩ := post
    change code = vals result at exits
    subst code
    exact .refl
  | step progress _ ih =>
    obtain ⟨next, step⟩ := progress
    exact step.steps.trans (ih next step)

private theorem singleResult (results : List Val) (types : results.map valTy = [some .i32]) :
    ∃ word : BitVec 32, results = [.i32 word] := by
  cases results with
  | nil => simp at types
  | cons value rest =>
    obtain rfl : rest = [] := by simpa using congrArg List.length types
    rcases value with ⟨⟨t, word⟩⟩ | ⟨⟩ | ⟨⟩
    · rcases t with t | t
      · cases t
        · exact ⟨word, rfl⟩
        · simp [valTy] at types
      · simp [valTy] at types
    · simp [valTy] at types
    · simp [valTy] at types

/-- Transfer a verified path of the quoted reader to the explicit call and store. -/
private theorem call_of_vcs {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {memoryAddr : Nat} {mem : MemInst}
    (F : Fns) (width : Nat) (out : ByteArray)
    (valid : AllValid F (genFunc (contract width) quoted 256))
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm quoted)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (preH : F.pr 0 mem.bytes [src, dst])
    (postH : ∀ bytes, F.pr2 0 mem.bytes bytes [src, dst] → bytes = out) :
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr { mem with bytes := out }, caller, [constI32 (BitVec.ofNat 32 width)]⟩ := by
  unfold Store.mem? at mapped
  obtain ⟨ma, memLink, rest⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨mi, memEntry, pair⟩ := Option.bind_eq_some_iff.mp rest
  rcases Prod.mk.inj (Option.some.inj pair) with ⟨rfl, rfl⟩
  change fi.module.mems[0]? = some ma at memLink
  let S := contract width
  let ρ : Env := ⟨(fun i => if i = 0 then src else dst), (fun _ => 0), fun _ => mi.bytes⟩
  have hm : MemOk S s fi.module (ρ.mem 0) := ⟨ma, mi, memLink, memEntry, rfl⟩
  have hg : GlobOk S s fi.module ρ := by simp [GlobOk, S, contract]
  have pre : (fspec F S instanceAddr fi).pre s [.i32 src, .i32 dst] :=
    ⟨instanceAt, by simp [Callees, S, contract], ρ, rfl, hm, hg, preH⟩
  have total : TFSpecAt P host instanceAddr (fspec F S instanceAddr fi) :=
    genFunc_tsound rfl code signature rfl rfl valid (by simp [CalleesValid, S, contract])
  let word := BitVec.ofNat 32 width
  let Q : Post H := fun t f o => t = s.setMem ma { mi with bytes := out } ∧
    f = caller ∧ o = .normal [.i32 word]
  have safe : TSafe P host Q
      ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩ := by
    apply TSafe.callIdx (vs₀ := []) (rest := []) (x := ⟨434⟩) slot instanceAt total pre
    intro final outcome call
    rcases call.2 with ⟨results, rfl, post⟩ | ⟨rfl, post⟩ | ⟨tag, rfl, post⟩
    · obtain ⟨bytes, globals, store, globalTypes, result, same, _, types, facts⟩ := post
      cases same
      obtain rfl : globals = [] := by simpa [S, contract] using globalTypes
      obtain ⟨observedWord, rfl⟩ := singleResult results types
      have observed := facts ρ rfl hm hg
      change observedWord = word ∧ F.pr2 0 mi.bytes bytes [src, dst] at observed
      obtain ⟨rfl, memory⟩ := observed
      have outEq := postH bytes memory
      subst bytes
      rw [setGs_nil] at store
      change _ = setM s fi.module out at store
      rw [setM_some memLink memEntry] at store
      exact .exit (.normal [.i32 word]) rfl ⟨store, rfl, rfl⟩
    · obtain ⟨_, _, _, _, _, impossible, _⟩ := post
      cases impossible
    · obtain ⟨_, _, _, _, _, impossible, _⟩ := post
      cases impossible
  exact reachesResult safe

end SixByteReader

private def sixByteValue (first second third fourth fifth sixth : UInt8) : Nat :=
  ((((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 +
    fourth.toNat % 128) * 128 + fifth.toNat % 128) * 128 + sixth.toNat

private structure SixByteInput (B : ByteArray) (src : BitVec 32) (first second third fourth fifth sixth : UInt8) : Prop where
  firstByte : B[src.toNat]? = some first
  secondByte : B[src.toNat + 1]? = some second
  thirdByte : B[src.toNat + 2]? = some third
  fourthByte : B[src.toNat + 3]? = some fourth
  fifthByte : B[src.toNat + 4]? = some fifth
  sixthByte : B[src.toNat + 5]? = some sixth
  firstContinues : 128 ≤ first.toNat
  secondContinues : 128 ≤ second.toNat
  thirdContinues : 128 ≤ third.toNat
  fourthContinues : 128 ≤ fourth.toNat
  fifthContinues : 128 ≤ fifth.toNat
  ends : sixth.toNat < 128

private theorem viewByte (B : ByteArray) (index : Nat) (byte : UInt8)
    (input : B[index]? = some byte) :
    (File.View.ofBytes ⟨B⟩).get? index = some byte := by
  have bound := (getElem?_eq_some_iff.mp input).choose
  simpa [File.View.ofBytes, File.View.get?, Silmaril.Formats.Bytes.length, bound] using input

private theorem readSixByte (B : ByteArray) (src : BitVec 32)
    (first second third fourth fifth sixth : UInt8)
    (input : SixByteInput B src first second third fourth fifth sixth) :
    Varint.read? (File.View.ofBytes ⟨B⟩) src.toNat =
      some (UInt64.ofNat (sixByteValue first second third fourth fifth sixth), src.toNat + 6) := by
  have firstContinues := Nat.not_lt.mpr input.firstContinues
  have secondContinues := Nat.not_lt.mpr input.secondContinues
  have thirdContinues := Nat.not_lt.mpr input.thirdContinues
  have fourthContinues := Nat.not_lt.mpr input.fourthContinues
  have fifthContinues := Nat.not_lt.mpr input.fifthContinues
  simp [Varint.read?, Varint.readNat?, Varint.readAux?, viewByte _ _ _ input.firstByte,
    viewByte _ _ _ input.secondByte, viewByte _ _ _ input.thirdByte, viewByte _ _ _ input.fourthByte,
    viewByte _ _ _ input.fifthByte, viewByte _ _ _ input.sixthByte, firstContinues, secondContinues,
    thirdContinues, fourthContinues, fifthContinues,
    input.ends, Nat.mod_eq_of_lt input.ends, sixByteValue, Nat.add_assoc]

open Silmaril.Wasm.Logic.Core (bytesAt getElem?_bytesAt leNat_cons load_eq)

private abbrev reader := SixByteReader.quoted

private def precondition (_ : Nat) (B : ByteArray) : List (BitVec 32) → Prop
  | [src, dst] => (∃ first second third fourth fifth sixth, SixByteInput B src first second third fourth fifth sixth) ∧ dst.toNat + 8 ≤ B.size
  | _ => False

private def postcondition (_ : Nat) (B final : ByteArray) : List (BitVec 32) → Prop
  | [src, dst] => ∃ first second third fourth fifth sixth, SixByteInput B src first second third fourth fifth sixth ∧
      final = Memory.writeSlice B dst.toNat (Memory.encodeLE 8 (sixByteValue first second third fourth fifth sixth))
  | _ => False

private def model : Fns := { pr := precondition, pr2 := postcondition }

private abbrev spec := SixByteReader.contract 6

private def generated : List Fm := genFunc spec reader 256

private theorem loadByte (B : ByteArray) (index : Nat) (byte : UInt8)
    (input : B[index]? = some byte) :
    ldW 32 1 .signed B index = byte.toBitVec.signExtend 32 := by
  have bound := (getElem?_eq_some_iff.mp input).choose
  have pick : B.data.toList[index]? = some byte := by
    rw [getElem?_pos B index bound] at input
    simpa [ByteArray.getElem_eq_getElem_data, getElem?_pos B.data index
      (show index < B.data.size from bound)] using input
  have contents : bytesAt B ⟨index, 1⟩ = [byte] := by
    apply List.ext_getElem?
    intro i
    cases i <;> simp [getElem?_bytesAt, pick]
  unfold ldW rd
  rw [load_eq (by omega), contents, leNat_cons]
  change (BitVec.ofNat 8 byte.toBitVec.toNat).signExtend 32 = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem signedContinues (byte : UInt8) (high : 128 ≤ byte.toNat) :
    (byte.toBitVec.signExtend 32).toInt ≤ -1 := by
  have sign : byte.toBitVec.msb = true := BitVec.msb_eq_true_iff_two_mul_ge.mpr (by
    rw [UInt8.toNat_toBitVec]
    omega)
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_msb_cond, sign]
  have bound := byte.toNat_lt
  simp only [↓reduceIte, UInt8.toNat_toBitVec]
  omega

private theorem signedEnds (byte : UInt8) (low : byte.toNat < 128) :
    -1 < (byte.toBitVec.signExtend 32).toInt := by
  have sign : byte.toBitVec.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
    rw [UInt8.toNat_toBitVec]
    omega)
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_of_msb sign]
  omega

private def octetWord (byte : UInt8) : BitVec 64 :=
  (byte.toBitVec.signExtend 32).setWidth 64 &&& 255#64

private theorem maskByte (byte : UInt8) : (octetWord byte).toNat = byte.toNat := by
  unfold octetWord
  rw [BitVec.toNat_and]
  change ((byte.toBitVec.signExtend 32).setWidth 64).toNat &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide), UInt8.toNat_toBitVec]
  have bound := byte.toNat_lt
  cases byte.toBitVec.msb <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem clearContinuation (a : BitVec 64) (lower : 128 ≤ a.toNat) (upper : a.toNat < 256) :
    (a ^^^ 128#64).toNat = a.toNat % 128 := by
  rw [BitVec.toNat_xor]
  change a.toNat ^^^ 128 = a.toNat % 128
  have upperPart : (a.toNat ^^^ 128) / 128 = 0 := by
    change (a.toNat ^^^ 128) / 2 ^ 7 = 0
    rw [Nat.xor_div_two_pow, show a.toNat / 2 ^ 7 = 1 by omega]
    rfl
  have lowPart : (a.toNat ^^^ 128) % 128 = a.toNat % 128 := by
    change (a.toNat ^^^ 128) % 2 ^ 7 = _
    rw [Nat.xor_mod_two_pow]
    exact Nat.xor_zero _
  omega

private theorem appendDigit (a b : BitVec 64) (high : a.toNat < 2 ^ 57) (low : b.toNat < 128) :
    (a <<< 7 ^^^ b).toNat = a.toNat * 128 + b.toNat := by
  rw [BitVec.toNat_xor, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show a.toNat * 2 ^ 7 < 2 ^ 64 by omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  change (a.toNat * 2 ^ 7 ^^^ b.toNat).testBit i =
    (a.toNat * 2 ^ 7 + b.toNat).testBit i
  rw [Nat.testBit_xor, Nat.testBit_mul_two_pow, Nat.mul_comm a.toNat,
    Nat.testBit_two_pow_mul_add _ (show b.toNat < 2 ^ 7 from low)]
  by_cases index : i < 7
  · simp [index, show ¬ 7 ≤ i by omega]
  · have zero : b.toNat.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le low (Nat.pow_le_pow_right (show 0 < 2 by decide) (show 7 ≤ i by omega)))
    simp [index, show 7 ≤ i by omega, zero]

private theorem moveCorrection {width : Nat}
    (shift : BitVec width → BitVec width)
    (distrib : ∀ a b, shift (a ^^^ b) = shift a ^^^ shift b) (a b c d mask : BitVec width) :
    (shift (shift (shift a ^^^ b) ^^^ c) ^^^ d) ^^^
      (shift (shift (shift mask)) ^^^ shift (shift mask) ^^^ shift mask) =
    shift (shift (shift (a ^^^ mask) ^^^ (b ^^^ mask)) ^^^ (c ^^^ mask)) ^^^ d := by
  simp only [distrib]
  ac_rfl

/-- The fourth-byte path's quoted correction moves to three continuation octets. -/
private theorem cancelThreeContinuationBits (a b c d : BitVec 64) :
    ((((a <<< 7 ^^^ b) <<< 7 ^^^ c) <<< 7 ^^^ d) ^^^ 270548992#64) =
      (((((a ^^^ 128#64) <<< 7 ^^^ (b ^^^ 128#64)) <<< 7 ^^^ (c ^^^ 128#64)) <<< 7) ^^^ d) := by
  let shift := fun x : BitVec 64 => x <<< (7 : Nat)
  have correction : 270548992#64 =
      (shift (shift (shift 128#64)) ^^^ shift (shift 128#64) ^^^ shift 128#64) := by decide +kernel
  rw [correction]
  exact moveCorrection shift (fun x y => BitVec.shiftLeft_xor_distrib x y 7) a b c d 128#64

open SqliteWasm.VarintContinuation (appendAfterContinuation)

/-- The bit-7 correction can be applied to the last octet before the XOR. -/
private theorem clearLastOctet (digits byte : BitVec 64) :
    (digits <<< 7 ^^^ byte) ^^^ 128#64 =
      digits <<< 7 ^^^ (byte ^^^ 128#64) :=
  BitVec.xor_assoc _ _ _

private theorem fourPendingCleared (a b c d : BitVec 64)
    (aLow : 128 ≤ a.toNat) (aHigh : a.toNat < 256)
    (bLow : 128 ≤ b.toNat) (bHigh : b.toNat < 256)
    (cLow : 128 ≤ c.toNat) (cHigh : c.toNat < 256)
    (dLow : 128 ≤ d.toNat) (dHigh : d.toNat < 256) :
    (((((a <<< 7 ^^^ b) <<< 7 ^^^ c) <<< 7 ^^^ d) ^^^ 270548992#64) ^^^ 128#64).toNat =
      ((a.toNat % 128 * 128 + b.toNat % 128) * 128 + c.toNat % 128) * 128 + d.toNat % 128 := by
  rw [cancelThreeContinuationBits, clearLastOctet]
  have first := clearContinuation a aLow aHigh
  have second := clearContinuation b bLow bHigh
  have third := clearContinuation c cLow cHigh
  have fourth := clearContinuation d dLow dHigh
  have pair := appendDigit (a ^^^ 128#64) (b ^^^ 128#64)
    (by rw [first]; omega) (by rw [second]; omega)
  rw [first, second] at pair
  have triple := appendDigit _ (c ^^^ 128#64) (by rw [pair]; omega) (by rw [third]; omega)
  rw [pair, third] at triple
  rw [appendDigit _ (d ^^^ 128#64) (by rw [triple]; omega) (by rw [fourth]; omega),
    triple, fourth]

private def fourthWord (a b c d : BitVec 64) : BitVec 64 :=
  ((((a <<< 7 ^^^ b) <<< 7 ^^^ c) <<< 7 ^^^ d) ^^^ 270548992#64)

/-- The last octet still carries its continuation bit until the next digit is read. -/
private def pendingWord (digits : Nat) (last : UInt8) : BitVec 64 :=
  (BitVec.ofNat 64 digits <<< 7) ^^^ octetWord last

private def advanceWord (word : BitVec 64) (next : UInt8) : BitVec 64 :=
  (word <<< 7 ^^^ octetWord next) ^^^ 16384#64

/-- The recurring 0x4000 step finalizes the preceding continuation octet
and leaves the just-loaded octet pending, whether it continues or terminates. -/
private theorem advancePending (digits : Nat) (last next : UInt8)
    (fits : digits < 2 ^ 57) (continues : 128 ≤ last.toNat) :
    advanceWord (pendingWord digits last) next =
      pendingWord (digits * 128 + last.toNat % 128) next := by
  unfold advanceWord pendingWord
  rw [appendAfterContinuation, BitVec.xor_assoc
    (BitVec.ofNat 64 digits <<< 7) (octetWord last) (128#64)]
  have shifted : ((BitVec.ofNat 64 digits <<< 7) ^^^ (octetWord last ^^^ 128#64)) =
      BitVec.ofNat 64 (digits * 128 + last.toNat % 128) := by
    have rawBounds := last.toNat_lt
    have cleared := clearContinuation (octetWord last)
      (by rwa [maskByte]) (by rw [maskByte]; exact rawBounds)
    rw [maskByte] at cleared
    have digitBound : (octetWord last ^^^ 128#64).toNat < 128 := by rw [cleared]; omega
    have digitPrefix : (BitVec.ofNat 64 digits).toNat = digits := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have total : digits * 128 + last.toNat % 128 < 2 ^ 64 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [appendDigit _ _ (by rwa [digitPrefix]) digitBound, digitPrefix, cleared,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt total]
  rw [shifted]

private theorem terminalPending (digits : Nat) (last : UInt8)
    (fits : digits < 2 ^ 57) (ends : last.toNat < 128) :
    (pendingWord digits last).toNat = digits * 128 + last.toNat := by
  have digitPrefix : (BitVec.ofNat 64 digits).toNat = digits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold pendingWord
  rw [appendDigit _ _ (by rwa [digitPrefix]) (by rwa [maskByte]), digitPrefix, maskByte]

private theorem decodeWord (first second third fourth fifth sixth : UInt8)
    (a : 128 ≤ first.toNat) (b : 128 ≤ second.toNat) (c : 128 ≤ third.toNat)
    (d : 128 ≤ fourth.toNat) (e : 128 ≤ fifth.toNat) (f : sixth.toNat < 128) :
    (advanceWord (advanceWord (fourthWord (octetWord first) (octetWord second)
      (octetWord third) (octetWord fourth)) fifth) sixth).toNat =
        sixByteValue first second third fourth fifth sixth := by
  let digits := ((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 +
    fourth.toNat % 128
  have fits : digits < 2 ^ 28 := by
    unfold digits
    omega
  have cleared : fourthWord (octetWord first) (octetWord second) (octetWord third)
      (octetWord fourth) ^^^ 128#64 = BitVec.ofNat 64 digits := by
    have normalized := fourPendingCleared (octetWord first) (octetWord second)
      (octetWord third) (octetWord fourth)
      (by rwa [maskByte]) (by rw [maskByte]; exact first.toNat_lt)
      (by rwa [maskByte]) (by rw [maskByte]; exact second.toNat_lt)
      (by rwa [maskByte]) (by rw [maskByte]; exact third.toNat_lt)
      (by rwa [maskByte]) (by rw [maskByte]; exact fourth.toNat_lt)
    rw [maskByte, maskByte, maskByte, maskByte] at normalized
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show digits < 2 ^ 64 by omega)]
    exact normalized
  have pending : advanceWord (fourthWord (octetWord first) (octetWord second)
      (octetWord third) (octetWord fourth)) fifth = pendingWord digits fifth := by
    unfold advanceWord pendingWord
    rw [appendAfterContinuation, cleared]
  rw [pending, advancePending _ _ _ (by omega) e, terminalPending _ _ (by omega) f]
  rfl

private theorem storeWord (B : ByteArray) (dst : BitVec 32) (word : BitVec 64)
    (bounds : dst.toNat + 8 ≤ B.size) :
    stW 64 8 B dst.toNat word = Memory.writeSlice B dst.toNat (Memory.encodeLE 8 word.toNat) := by
  rw [stW, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bounds]
  simp

private theorem valid : AllValid model generated := by
  vcgen4_reduce
  vcgen4_den
  simp only [IntType.width, model, precondition, postcondition]
  and_intros
  all_goals vcgen4_vars
  all_goals intro h
  all_goals repeat' cases_type And
  all_goals subst_vars
  all_goals try assumption
  all_goals obtain ⟨first, second, third, fourth, fifth, sixth, input⟩ :=
    (show ∃ a b c d e f, SixByteInput M0 v0 a b c d e f from by assumption)
  all_goals have firstLoad := loadByte _ _ _ input.firstByte
  all_goals have secondLoad := loadByte _ _ _ input.secondByte
  all_goals have thirdLoad := loadByte _ _ _ input.thirdByte
  all_goals have fourthLoad := loadByte _ _ _ input.fourthByte
  all_goals have fifthLoad := loadByte _ _ _ input.fifthByte
  all_goals have sixthLoad := loadByte _ _ _ input.sixthByte
  all_goals have firstContinues := signedContinues _ input.firstContinues
  all_goals have secondContinues := signedContinues _ input.secondContinues
  all_goals have thirdContinues := signedContinues _ input.thirdContinues
  all_goals have fourthContinues := signedContinues _ input.fourthContinues
  all_goals have fifthContinues := signedContinues _ input.fifthContinues
  all_goals have ends := signedEnds _ input.ends
  all_goals simp only [Nat.add_zero, firstLoad, secondLoad, thirdLoad, fourthLoad, fifthLoad, sixthLoad,
    show (4294967295#32).toInt = -1 from rfl] at *
  all_goals try omega
  · have bound := (getElem?_eq_some_iff.mp input.firstByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.secondByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.thirdByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.fourthByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.fifthByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.sixthByte).choose
    omega
  · refine ⟨?_, first, second, third, fourth, fifth, sixth, input, ?_⟩
    · rw [BitVec.add_comm v0 (5#32), BitVec.add_sub_cancel]
      rfl
    · rw [storeWord _ _ _ (by assumption)]
      change Memory.writeSlice _ _ (Memory.encodeLE 8
        (advanceWord (advanceWord (fourthWord (octetWord first) (octetWord second)
          (octetWord third) (octetWord fourth)) fifth) sixth).toNat) = _
      rw [decodeWord first second third fourth fifth sixth input.firstContinues input.secondContinues
        input.thirdContinues input.fourthContinues input.fifthContinues input.ends]

/-- The six-byte branch of the pinned reactor reader, including overlong encodings.
All six source lookups are on the initial callee memory. The eight-byte output may
overlap those bytes. The call returns i32 6 in the original caller frame. -/
theorem getVarint_sixByte {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {first second third fourth fifth sixth : UInt8} {memoryAddr : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 434 = some fn)
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (firstByte : mem.bytes[src.toNat]? = some first)
    (secondByte : mem.bytes[src.toNat + 1]? = some second)
    (thirdByte : mem.bytes[src.toNat + 2]? = some third)
    (fourthByte : mem.bytes[src.toNat + 3]? = some fourth)
    (fifthByte : mem.bytes[src.toNat + 4]? = some fifth)
    (sixthByte : mem.bytes[src.toNat + 5]? = some sixth)
    (firstContinues : 128 ≤ first.toNat) (secondContinues : 128 ≤ second.toNat)
    (thirdContinues : 128 ≤ third.toNat) (fourthContinues : 128 ≤ fourth.toNat)
    (fifthContinues : 128 ≤ fifth.toNat) (ends : sixth.toNat < 128)
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    let value := ((((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 +
      fourth.toNat % 128) * 128 + fifth.toNat % 128) * 128 + sixth.toNat
    Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat =
        some (UInt64.ofNat value, src.toNat + 6) ∧
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 value) },
        caller, [constI32 6]⟩ := by
  have same := Option.some.inj (selected.symm.trans SixByteReader.quotedSelected)
  subst fn
  have input : SixByteInput mem.bytes src first second third fourth fifth sixth :=
    ⟨firstByte, secondByte, thirdByte, fourthByte, fifthByte, sixthByte, firstContinues, secondContinues,
      thirdContinues, fourthContinues, fifthContinues, ends⟩
  refine ⟨readSixByte _ _ _ _ _ _ _ _ input, ?_⟩
  refine SixByteReader.call_of_vcs model 6 _ valid slot instanceAt code signature mapped
    ⟨⟨first, second, third, fourth, fifth, sixth, input⟩, inBounds⟩ ?_
  intro bytes observed
  obtain ⟨a, b, c, d, e, f, observedInput, memory⟩ := observed
  obtain rfl : a = first := Option.some.inj (observedInput.firstByte.symm.trans input.firstByte)
  obtain rfl : b = second := Option.some.inj (observedInput.secondByte.symm.trans input.secondByte)
  obtain rfl : c = third := Option.some.inj (observedInput.thirdByte.symm.trans input.thirdByte)
  obtain rfl : d = fourth := Option.some.inj (observedInput.fourthByte.symm.trans input.fourthByte)
  obtain rfl : e = fifth := Option.some.inj (observedInput.fifthByte.symm.trans input.fifthByte)
  obtain rfl : f = sixth := Option.some.inj (observedInput.sixthByte.symm.trans input.sixthByte)
  exact memory

#print axioms getVarint_sixByte

end SqliteWasm
