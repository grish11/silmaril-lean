module

public import Silmaril.Wasm.Binary.Core.LocalSerialize.Defs
import Silmaril.Wasm.Binary.Core.PassiveSerialize.Thms

public section

namespace Silmaril.Proofs.Wasm.Binary.Core.LocalSerialize

open Silmaril.Wasm hiding Shape
open Silmaril.Wasm.Binary (magic version)
open Silmaril.Wasm.Binary.Core.Decode Silmaril.Wasm.Binary.Core.LocalSerialize
open Silmaril.Wasm.Binary.Core.PassiveSerialize.Reader
open Silmaril.Wasm.Tools.Meta (encU32)

private theorem bind_at {α β : Type} {reader : DecodeM α} {nextReader : α → DecodeM β}
    {start next : Cursor} {value : α} (ok : reader.run start = .ok (value, next)) :
    (reader >>= nextReader).run start = (nextReader value).run next := by
  rw [StateT.run_bind, ok]
  rfl

private theorem rest_next {bytes : ByteArray} {pos : Nat} {part rest : List UInt8}
    (atPrefix : (Cursor.mk bytes pos).rest = part ++ rest) :
    (Cursor.mk bytes (pos + part.length)).rest = rest := by
  simp only [Cursor.rest] at atPrefix ⊢
  rw [← List.drop_drop, atPrefix, List.drop_left]

private theorem remaining_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atRest : (Cursor.mk bytes pos).rest = rest) :
    remaining.run ⟨bytes, pos⟩ = .ok (rest.length, ⟨bytes, pos⟩) := by
  have size := congrArg List.length atRest
  simp [Cursor.rest] at size
  change Except.ok (bytes.size - pos, Cursor.mk bytes pos) = _
  rw [size]

private theorem peek_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atRest : (Cursor.mk bytes pos).rest = rest) :
    peekByte.run ⟨bytes, pos⟩ = .ok (rest.head?, ⟨bytes, pos⟩) := by
  have first := congrArg (·[0]?) atRest
  simp only [Cursor.rest, List.getElem?_drop, Nat.add_zero, Array.getElem?_toList] at first
  change Except.ok (bytes.data[pos]?, Cursor.mk bytes pos) = _
  rw [first]
  cases rest <;> rfl

private theorem idx_at {kind : IndexKind} {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (index : Idx kind) (atIndex : (Cursor.mk bytes pos).rest = encU32 index.toNat ++ rest) :
    (readIdx : DecodeM (Idx kind)).run ⟨bytes, pos⟩ =
      .ok (index, ⟨bytes, pos + (encU32 index.toNat).length⟩) := by
  obtain ⟨⟨value, bound⟩⟩ := index
  unfold readIdx
  rw [bind_at (u32_at bound atIndex), dite_eq_left bound]
  rfl

private theorem count_at {bytes : ByteArray} {pos count : Nat} {rest : List UInt8}
    (atCount : (Cursor.mk bytes pos).rest = encU32 count ++ rest)
    (bound : count < 2 ^ 32) (fits : count ≤ rest.length) :
    readCount.run ⟨bytes, pos⟩ = .ok (count, ⟨bytes, pos + (encU32 count).length⟩) := by
  unfold readCount
  rw [bind_at (u32_at bound atCount), bind_at (remaining_at (rest_next atCount)), ite_eq_left fits]
  rfl

private theorem encZero : encU32 0 = [0] := by decide +kernel
private theorem encOne : encU32 1 = [1] := by decide +kernel

private theorem word_length_le (fuel : Nat) {value : Nat} (positive : 0 < fuel)
    (bound : value < 128 ^ fuel) : (encU32 value).length ≤ fuel := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    rw [encU32]
    by_cases small : value < 128
    · rw [ite_eq_left small]
      exact Nat.succ_le_succ (Nat.zero_le _)
    · rw [ite_eq_right small, List.length_cons]
      have quotient : value / 128 < 128 ^ fuel := by
        apply Nat.div_lt_of_lt_mul
        simpa only [Nat.pow_succ, Nat.mul_comm] using bound
      have positive : 0 < fuel := by
        by_contra empty
        have : fuel = 0 := by omega
        subst fuel
        simp at bound
        omega
      exact Nat.succ_le_succ (ih positive quotient)

theorem fits_of_bounds {locals index : Nat} (cap : locals ≤ maxLocals) (ref : index < locals) :
    Fits locals index := by
  have localCap : locals ≤ 50000 := cap
  have countLen := word_length_le 3 (value := locals) (by decide) (by omega)
  have indexLen := word_length_le 3 (value := index) (by decide) (by omega)
  have bodyLen : (bodyBytes locals index).length ≤ 10 := by simp [bodyBytes]; omega
  have sizeLen : (encU32 (bodyBytes locals index).length).length = 1 := by
    rw [encU32, ite_eq_left (by omega : (bodyBytes locals index).length < 128)]
    rfl
  have codeLen : (codeBytes locals index).length ≤ 12 := by simp [codeBytes, sizeLen]; omega
  exact ⟨by omega, cap, ref, by omega, by omega⟩

private theorem vec_one_at {α : Type} {readItem : DecodeM α} {item : α} {bytes : ByteArray}
    {pos finish : Nat} {rest : List UInt8} (atCount : (Cursor.mk bytes pos).rest = 1 :: rest)
    (nonempty : rest ≠ []) (atItem : readItem.run ⟨bytes, pos + 1⟩ = .ok (item, ⟨bytes, finish⟩)) :
    (readVec readItem).run ⟨bytes, pos⟩ = .ok ([item], ⟨bytes, finish⟩) := by
  have count := count_at (count := 1) (rest := rest) (by rw [encOne]; exact atCount) (by decide)
    (List.length_pos_iff.mpr nonempty)
  rw [encOne] at count
  unfold readVec
  rw [bind_at count, readVec.go]
  change (readItem >>= _).run ⟨bytes, pos + 1⟩ = _
  rw [bind_at atItem, readVec.go]
  rfl

private theorem vec_zero_at {α : Type} (readItem : DecodeM α) {bytes : ByteArray} {pos : Nat}
    {rest : List UInt8} (atCount : (Cursor.mk bytes pos).rest = 0 :: rest) :
    (readVec readItem).run ⟨bytes, pos⟩ = .ok ([], ⟨bytes, pos + 1⟩) := by
  have count := count_at (count := 0) (rest := rest) (by rw [encZero]; exact atCount) (by decide) (Nat.zero_le _)
  rw [encZero] at count
  unfold readVec
  rw [bind_at count, readVec.go]
  rfl

private theorem i32_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atByte : (Cursor.mk bytes pos).rest = 0x7f :: rest) :
    readValType.run ⟨bytes, pos⟩ = .ok (.i32, ⟨bytes, pos + 1⟩) := by
  unfold readValType
  rw [bind_at (peek_at atByte)]
  change (readByte >>= fun _ => pure Wasm.ValType.i32).run _ = _
  rw [bind_at (byte_at atByte)]
  rfl

private theorem expr_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (index : LocalIdx) (atOp : (Cursor.mk bytes pos).rest = [0x20] ++ encU32 index.toNat ++ [0x0b] ++ rest) :
    readExpr.run ⟨bytes, pos⟩ = .ok ([.localGet index], ⟨bytes, pos + 1 + (encU32 index.toNat).length + 1⟩) := by
  have atOp' : (Cursor.mk bytes pos).rest = 0x20 :: (encU32 index.toNat ++ (0x0b :: rest)) := by
    simpa [List.append_assoc] using atOp
  have atIndex : (Cursor.mk bytes (pos + 1)).rest = encU32 index.toNat ++ (0x0b :: rest) :=
    rest_next (part := [0x20]) atOp'
  have atEnd := rest_next atIndex
  have remainingEq := remaining_at atOp
  have enough : ∃ fuel, ([0x20] ++ encU32 index.toNat ++ [0x0b] ++ rest : List UInt8).length = fuel + 1 :=
    ⟨(encU32 index.toNat).length + 1 + rest.length, by simp; omega⟩
  obtain ⟨fuel, fuelEq⟩ := enough
  have atInstr : (readPlain 0x20).run ⟨bytes, pos + 1⟩ =
      .ok (.localGet index, ⟨bytes, pos + 1 + (encU32 index.toNat).length⟩) := by
    change (readIdx >>= fun index => pure (Wasm.Instr.localGet index)).run _ = _
    rw [bind_at (idx_at index atIndex)]
    rfl
  have atSeq : (readSeq ((fuel + 1) + 1)).run ⟨bytes, pos⟩ =
      .ok (([.localGet index], 0x0b), ⟨bytes, pos + 1 + (encU32 index.toNat).length + 1⟩) := by
    rw [readSeq, bind_at (byte_at atOp')]
    change (readPlain 0x20 >>= _).run ⟨bytes, pos + 1⟩ = _
    have ending : (readSeq (fuel + 1)).run ⟨bytes, pos + 1 + (encU32 index.toNat).length⟩ =
        .ok (([], 0x0b), ⟨bytes, pos + 1 + (encU32 index.toNat).length + 1⟩) := by
      rw [readSeq, bind_at (byte_at atEnd)]
      rfl
    rw [bind_at atInstr, bind_at ending]
    rfl
  unfold readExpr
  rw [bind_at remainingEq, fuelEq, bind_at atSeq]
  rfl

private theorem group_at (shape : Shape) {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atGroup : (Cursor.mk bytes pos).rest = encU32 shape.locals ++ (0x7f :: rest)) :
    (do let count ← readU 32; let ty ← readValType; pure (count, ty) : DecodeM (Nat × Wasm.ValType)).run
      ⟨bytes, pos⟩ = .ok ((shape.locals, .i32), ⟨bytes, pos + (encU32 shape.locals).length + 1⟩) := by
  rw [bind_at (u32_at shape.fits.localCount atGroup), bind_at (i32_at (rest_next atGroup))]
  rfl

theorem code_at (shape : Shape) {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atCode : (Cursor.mk bytes pos).rest =
      encU32 (bodyBytes shape.locals shape.index).length ++ bodyBytes shape.locals shape.index ++ rest) :
    readCode.run ⟨bytes, pos⟩ = .ok ((List.replicate shape.locals .i32, [.localGet shape.localIndex]),
      ⟨bytes, pos + (encU32 (bodyBytes shape.locals shape.index).length ++ bodyBytes shape.locals shape.index).length⟩) := by
  let body := bodyBytes shape.locals shape.index
  let bodyStart := pos + (encU32 body.length).length
  let exprStart := bodyStart + 1 + (encU32 shape.locals).length + 1
  have atLength : (Cursor.mk bytes pos).rest = encU32 body.length ++ (body ++ rest) := by
    simpa [body, List.append_assoc] using atCode
  have atBody : (Cursor.mk bytes bodyStart).rest = body ++ rest := rest_next atLength
  have atCount : (Cursor.mk bytes bodyStart).rest = 1 :: (encU32 shape.locals ++
      (0x7f :: ([0x20] ++ encU32 shape.index ++ [0x0b] ++ rest))) := by
    simpa [body, bodyBytes, List.append_assoc] using atBody
  have atGroup := rest_next (part := [1]) atCount
  have atExpr : (Cursor.mk bytes exprStart).rest = [0x20] ++ encU32 shape.localIndex.toNat ++ [0x0b] ++ rest := by
    exact rest_next (part := [0x7f]) (rest_next atGroup)
  have atFinish := rest_next (part := [0x20] ++ encU32 shape.localIndex.toNat ++ [0x0b])
    (by simpa [List.append_assoc] using atExpr)
  have endOffset : exprStart + ([0x20] ++ encU32 shape.localIndex.toNat ++ [0x0b]).length =
      exprStart + 1 + (encU32 shape.localIndex.toNat).length + 1 := by simp; omega
  rw [endOffset] at atFinish
  have large : (bodyBytes shape.locals shape.index).length ≤ (body ++ rest).length := by
    change body.length ≤ (body ++ rest).length
    simp
  have check : ((body ++ rest).length - rest.length == (bodyBytes shape.locals shape.index).length) = true := by
    change ((body ++ rest).length - rest.length == body.length) = true
    simp
  unfold readCode
  rw [bind_at (u32_at shape.fits.bodySize atLength), bind_at (remaining_at atBody)]
  rw [ite_eq_left large]
  rw [bind_at (vec_one_at atCount (by simp) (group_at shape atGroup))]
  simp only [List.foldl_cons, Nat.zero_add, List.foldl_nil, shape.fits.decoderCap,
    ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [bind_at (expr_at shape.localIndex atExpr), bind_at (remaining_at atFinish), ite_eq_left check]
  have offset : exprStart + 1 + (encU32 shape.localIndex.toNat).length + 1 =
      pos + (encU32 (bodyBytes shape.locals shape.index).length ++ bodyBytes shape.locals shape.index).length := by
    simp [exprStart, bodyStart, body, bodyBytes, Shape.localIndex, Idx.toNat]
    omega
  rw [← offset]
  rfl

private theorem type_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atType : (Cursor.mk bytes pos).rest = 0x60 :: 0 :: 1 :: 0x7f :: rest) :
    readRecType.run ⟨bytes, pos⟩ = .ok (signature, ⟨bytes, pos + 4⟩) := by
  have atParam := rest_next (part := [0x60]) atType
  have atResult := rest_next (part := [0]) atParam
  have atVal := rest_next (part := [1]) atResult
  change (Cursor.mk bytes (pos + 1)).rest = _ at atParam
  change (Cursor.mk bytes (pos + 1 + 1)).rest = _ at atResult
  change (Cursor.mk bytes (pos + 1 + 1 + 1)).rest = _ at atVal
  have comp : readCompType.run ⟨bytes, pos⟩ = .ok (.func ⟨[], [.i32]⟩, ⟨bytes, pos + 4⟩) := by
    unfold readCompType
    rw [bind_at (byte_at atType)]
    change (readVec readValType >>= _).run ⟨bytes, pos + 1⟩ = _
    rw [bind_at (vec_zero_at readValType atParam), bind_at (vec_one_at atResult (by simp) (i32_at atVal))]
    rfl
  have sub : readSubType.run ⟨bytes, pos⟩ = .ok (⟨true, [], .func ⟨[], [.i32]⟩⟩, ⟨bytes, pos + 4⟩) := by
    unfold readSubType
    rw [bind_at (peek_at atType)]
    change (readCompType >>= _).run ⟨bytes, pos⟩ = _
    rw [bind_at comp]
    rfl
  unfold readRecType
  rw [bind_at (peek_at atType)]
  change (readSubType >>= _).run ⟨bytes, pos⟩ = _
  rw [bind_at sub]
  rfl

private theorem export_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atExport : (Cursor.mk bytes pos).rest = 1 :: 0x66 :: 0 :: 0 :: rest) :
    readExport.run ⟨bytes, pos⟩ = .ok (exportF, ⟨bytes, pos + 4⟩) := by
  have atName := rest_next (part := [1]) atExport
  have enough : pos + 1 ≤ bytes.size := by
    have length := congrArg List.length atExport
    simp [Cursor.rest] at length
    omega
  have count := count_at (count := 1) (rest := 0x66 :: 0 :: 0 :: rest)
    (by rw [encOne]; exact atExport) (by decide) (by simp)
  rw [encOne] at count
  have name : readName.run ⟨bytes, pos⟩ = .ok ("f", ⟨bytes, pos + 2⟩) := by
    have nameBytes := bytes_at (part := [0x66]) atName enough
    change (readBytes 1).run ⟨bytes, pos + ([1] : List UInt8).length⟩ = _ at nameBytes
    unfold readName
    rw [bind_at count, bind_at nameBytes]
    rfl
  have atKind := rest_next (part := [1, 0x66]) atExport
  have atIndex := rest_next (part := [0]) atKind
  change (Cursor.mk bytes (pos + 2)).rest = _ at atKind
  change (Cursor.mk bytes (pos + 2 + 1)).rest = _ at atIndex
  have index := idx_at (⟨0⟩ : FuncIdx) (rest := rest) (by rw [show (⟨0⟩ : FuncIdx).toNat = 0 from rfl, encZero]; exact atIndex)
  rw [show (⟨0⟩ : FuncIdx).toNat = 0 from rfl, encZero] at index
  unfold readExport
  rw [bind_at name, bind_at (byte_at atKind)]
  change ((readIdx : DecodeM FuncIdx) >>= _).run ⟨bytes, pos + 2 + 1⟩ = _
  rw [bind_at index]
  rfl

private theorem section_at {bytes : ByteArray} {pos fuel last width : Nat} {id : UInt8}
    {part rest : List UInt8} {before after : Sections}
    (idNonzero : id.toNat ≠ 0) (rank : last < sectionRank id.toNat)
    (sizeBound : part.length < 2 ^ 32) (sizeWidth : (encU32 part.length).length = width)
    (atSection : (Cursor.mk bytes pos).rest = id :: (encU32 part.length ++ (part ++ rest)))
    (body : (readSectionBody id.toNat before).run ⟨bytes, pos + 1 + width⟩ =
      .ok (after, ⟨bytes, pos + 1 + width + part.length⟩)) :
    (readModule.go (fuel + 1) last before).run ⟨bytes, pos⟩ =
      (readModule.go fuel (sectionRank id.toNat) after).run
        ⟨bytes, pos + 1 + width + part.length⟩ := by
  subst width
  have atSize := rest_next (part := [id]) atSection
  have atBody := rest_next atSize
  have atEnd := rest_next atBody
  change (Cursor.mk bytes (pos + 1)).rest = _ at atSize
  change (Cursor.mk bytes (pos + 1 + (encU32 part.length).length)).rest = _ at atBody
  change (Cursor.mk bytes (pos + 1 + (encU32 part.length).length + part.length)).rest = _ at atEnd
  have available : part.length ≤ (part ++ rest).length := by simp
  have sizeCheck : (((part ++ rest).length - rest.length) == part.length) = true := by simp
  have notDone : ¬ ((id :: (encU32 part.length ++ (part ++ rest))).length == 0) = true := by simp
  have notCustom : ¬ (id.toNat == 0) = true := by simpa using idNonzero
  rw [readModule.go, bind_at (remaining_at atSection), ite_eq_right notDone,
    bind_at (byte_at atSection), bind_at (u32_at sizeBound atSize), bind_at (remaining_at atBody),
    ite_eq_left available, ite_eq_right notCustom, ite_eq_left rank, bind_at body,
    bind_at (remaining_at atEnd), ite_eq_left sizeCheck]

private def firstSections : Sections := { types := [signature] }
private def secondSections : Sections := { firstSections with funcTypes := [⟨0⟩] }
private def thirdSections : Sections := { secondSections with exports := [exportF] }

private theorem sectionType_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atType : (Cursor.mk bytes pos).rest = 1 :: 0x60 :: 0 :: 1 :: 0x7f :: rest) :
    (readSectionBody 1 {}).run ⟨bytes, pos⟩ = .ok (firstSections, ⟨bytes, pos + 5⟩) := by
  change (readVec readRecType >>= _).run ⟨bytes, pos⟩ = _
  rw [bind_at (vec_one_at atType (by simp) (type_at (rest_next (part := [1]) atType)))]
  rfl

private theorem sectionFunc_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atFunc : (Cursor.mk bytes pos).rest = 1 :: 0 :: rest) :
    (readSectionBody 3 firstSections).run ⟨bytes, pos⟩ = .ok (secondSections, ⟨bytes, pos + 2⟩) := by
  have index := idx_at (⟨0⟩ : TypeIdx) (rest := rest)
    (by rw [show (⟨0⟩ : TypeIdx).toNat = 0 from rfl, encZero]; exact rest_next (part := [1]) atFunc)
  rw [show (⟨0⟩ : TypeIdx).toNat = 0 from rfl, encZero] at index
  change (readVec (readIdx : DecodeM TypeIdx) >>= _).run ⟨bytes, pos⟩ = _
  rw [bind_at (vec_one_at atFunc (by simp) index)]
  rfl

private theorem sectionExport_at {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atExport : (Cursor.mk bytes pos).rest = 1 :: 1 :: 0x66 :: 0 :: 0 :: rest) :
    (readSectionBody 7 secondSections).run ⟨bytes, pos⟩ = .ok (thirdSections, ⟨bytes, pos + 5⟩) := by
  change (readVec readExport >>= _).run ⟨bytes, pos⟩ = _
  rw [bind_at (vec_one_at atExport (by simp) (export_at (rest_next (part := [1]) atExport)))]
  rfl

private def completeSections (shape : Shape) : Sections :=
  { thirdSections with code := [((rawFunc shape).locals, (rawFunc shape).body)] }

private theorem sectionCode_at (shape : Shape) {bytes : ByteArray} {pos : Nat} {rest : List UInt8}
    (atCode : (Cursor.mk bytes pos).rest = codeBytes shape.locals shape.index ++ rest) :
    (readSectionBody 10 thirdSections).run ⟨bytes, pos⟩ =
      .ok (completeSections shape, ⟨bytes, pos + (codeBytes shape.locals shape.index).length⟩) := by
  let body := bodyBytes shape.locals shape.index
  have atCount : (Cursor.mk bytes pos).rest = 1 :: (encU32 body.length ++ body ++ rest) := by
    simpa [codeBytes, body, List.append_assoc] using atCode
  have nonempty : encU32 body.length ++ body ++ rest ≠ [] := by simp [body, bodyBytes]
  have vec := vec_one_at atCount nonempty (code_at shape (rest_next (part := [1]) atCount))
  change (readVec readCode >>= _).run ⟨bytes, pos⟩ = _
  rw [bind_at vec]
  have offset : pos + 1 + (encU32 body.length ++ body).length = pos + (codeBytes shape.locals shape.index).length := by
    simp [body, codeBytes]
    omega
  rw [offset]
  rfl

theorem decode_encode (shape : Shape) : Binary.Core.decode? (encode shape) = some (raw shape) := by
  let code := codeBytes shape.locals shape.index
  let tail := [10] ++ encU32 code.length ++ code
  let bytes := encode shape
  let finish := 27 + (encU32 code.length).length + code.length
  have byteList : bytes.data.toList = bytesBeforeCode ++ tail := by simp [bytes, encode, tail, code, List.append_assoc]
  have fixedSize : bytesBeforeCode.length = 26 := rfl
  have sizeEq : bytes.size = finish := by
    have size := congrArg List.length byteList
    simp [tail, fixedSize] at size
    dsimp [finish]
    omega
  have restAt (pos : Nat) (bound : pos ≤ 26) :
      (Cursor.mk bytes pos).rest = bytesBeforeCode.drop pos ++ tail := by
    change bytes.data.toList.drop pos = _
    rw [byteList, List.drop_append_of_le_length (fixedSize ▸ bound)]
  have headerRest : (Cursor.mk bytes 0).rest = (magic ++ version) ++ (bytesBeforeCode.drop 8 ++ tail) := by
    rw [restAt 0 (by decide)]
    rfl
  have header := bytes_at headerRest (Nat.zero_le _)
  have headerOk : readHeader.run ⟨bytes, 0⟩ = .ok ((), ⟨bytes, 8⟩) := by
    change (readBytes 8).run ⟨bytes, 0⟩ = _ at header
    unfold readHeader
    rw [bind_at header]
    rfl
  have atType : (Cursor.mk bytes 8).rest = 1 :: (encU32 5 ++
      ([1, 0x60, 0, 1, 0x7f] ++ ([3, 2, 1, 0, 7, 5, 1, 1, 0x66, 0, 0] ++ tail))) := by
    rw [restAt 8 (by decide), encU32]
    rfl
  have typeBody : (Cursor.mk bytes 10).rest = 1 :: 0x60 :: 0 :: 1 :: 0x7f ::
      ([3, 2, 1, 0, 7, 5, 1, 1, 0x66, 0, 0] ++ tail) := restAt 10 (by decide)
  have atFunc : (Cursor.mk bytes 15).rest = 3 :: (encU32 2 ++ ([1, 0] ++ ([7, 5, 1, 1, 0x66, 0, 0] ++ tail))) := by
    rw [restAt 15 (by decide), encU32]
    rfl
  have funcBody : (Cursor.mk bytes 17).rest = 1 :: 0 :: ([7, 5, 1, 1, 0x66, 0, 0] ++ tail) := restAt 17 (by decide)
  have atExport : (Cursor.mk bytes 19).rest = 7 :: (encU32 5 ++ ([1, 1, 0x66, 0, 0] ++ tail)) := by
    rw [restAt 19 (by decide), encU32]
    rfl
  have exportBody : (Cursor.mk bytes 21).rest = 1 :: 1 :: 0x66 :: 0 :: 0 :: tail := restAt 21 (by decide)
  have atCode : (Cursor.mk bytes 26).rest = 10 :: (encU32 code.length ++ (code ++ [])) := by
    have dropped : bytesBeforeCode.drop 26 = [] := rfl
    simpa [tail, dropped, List.append_assoc] using restAt 26 (by decide)
  have codeBody : (Cursor.mk bytes (27 + (encU32 code.length).length)).rest = code ++ [] :=
    rest_next (rest_next (part := [10]) atCode)
  have atEnd : (Cursor.mk bytes finish).rest = [] := rest_next codeBody
  have remain := remaining_at atEnd
  have fuelEq : bytes.size = finish - 4 + 4 := by rw [sizeEq]; dsimp [finish]; omega
  let fuel := finish - 4
  have go : (readModule.go bytes.size 0 {}).run ⟨bytes, 8⟩ = .ok (completeSections shape, ⟨bytes, finish⟩) := by
    rw [fuelEq]
    change (readModule.go (fuel + 3 + 1) 0 {}).run ⟨bytes, 8⟩ = _
    have first := section_at (fuel := fuel + 3) (last := 0) (width := 1) (part := [1, 0x60, 0, 1, 0x7f])
      (by decide) (by decide) (by decide) (by decide +kernel) atType (sectionType_at typeBody)
    have second := section_at (fuel := fuel + 2) (last := 1) (width := 1) (part := [1, 0])
      (by decide) (by decide) (by decide) (by decide +kernel) atFunc (sectionFunc_at funcBody)
    have third := section_at (fuel := fuel + 1) (last := 3) (width := 1) (part := [1, 1, 0x66, 0, 0])
      (by decide) (by decide) (by decide) (by decide +kernel) atExport (sectionExport_at exportBody)
    have fourth := section_at (fuel := fuel) (last := 8) (part := code)
      (by decide) (by decide) shape.fits.codeSize rfl atCode (sectionCode_at shape codeBody)
    rw [first]
    change (readModule.go (fuel + 2 + 1) 1 firstSections).run ⟨bytes, 15⟩ = _
    rw [second]
    change (readModule.go (fuel + 1 + 1) 3 secondSections).run ⟨bytes, 19⟩ = _
    rw [third]
    change (readModule.go (fuel + 1) 8 thirdSections).run ⟨bytes, 26⟩ = _
    rw [fourth]
    change (readModule.go fuel 12 (completeSections shape)).run ⟨bytes, finish⟩ = _
    generalize fuel = leftover
    cases leftover with
    | zero => rfl
    | succ more => rw [readModule.go, bind_at remain]; rfl
  have getAt : (get : DecodeM Cursor).run ⟨bytes, 8⟩ = .ok (⟨bytes, 8⟩, ⟨bytes, 8⟩) := rfl
  have moduleOk : readModule.run ⟨bytes, 0⟩ = .ok (raw shape, ⟨bytes, finish⟩) := by
    unfold readModule
    rw [bind_at headerOk, bind_at getAt, bind_at go, bind_at remain]
    simp [completeSections, thirdSections, secondSections, firstSections, Binary.Core.codesDataIdxs,
      Binary.Core.Expr.dataIdxs, Binary.Core.Instr.dataIdxs, Binary.Core.zipFuncs, raw, metadata, rawFunc]
    rfl
  unfold Binary.Core.decode? decodeModule StateT.run'
  change (match Prod.fst <$> readModule.run ⟨bytes, 0⟩ with | .ok mod => some mod | .error _ => none) = _
  rw [moduleOk]
  rfl

theorem raw_extract {mod : Wasm.Module} (fits : Serializable mod) : raw (extract mod fits) = mod := by
  obtain ⟨shape, rfl⟩ := fits
  simp [extract, raw, rawFunc, Shape.localIndex, Idx.toNat]

theorem decodeShape_encode (shape : Shape) : decodeShape? (encode shape) = some shape := by
  have accepted : accept? (raw shape) = some ⟨shape, rfl⟩ := by
    cases shape with
    | mk locals index fits => simp [raw, rawFunc, metadata, accept?, Shape.localIndex, Idx.toNat, fits]
  unfold decodeShape?
  rw [decode_encode]
  change ((accept? (raw shape)).bind fun accepted => some accepted.val) = _
  rw [accepted]
  rfl

theorem decodeShape_sound {bytes : ByteArray} {shape : Shape} (ok : decodeShape? bytes = some shape) :
    Binary.Core.decode? bytes = some (raw shape) := by
  obtain ⟨mod, decoded, accepted⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨checked, _, equal⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj equal
  rw [decoded, checked.property]

end Silmaril.Proofs.Wasm.Binary.Core.LocalSerialize
