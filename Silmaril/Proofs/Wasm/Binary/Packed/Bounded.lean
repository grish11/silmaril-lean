module

public import Silmaril.Wasm.Binary.Packed.Bounded.Defs
public import Silmaril.Wasm.Binary.Packed.Thms
public import Silmaril.Wasm.Component.ChunkedDecode.Thms

public section

namespace Silmaril.Proofs.Wasm.Binary.Packed.Bounded

open Silmaril.Wasm.Binary Silmaril.Wasm.Component.ChunkedDecode
open Silmaril.Wasm.Component.Chunked (arr runAll)
open Core.Decode
open Silmaril.Wasm.Binary.Packed (Agrees Reader readHeader_agrees readU_agrees)
open Silmaril.Wasm.Binary.Packed.Bounded (CodeEntry assemble finish readBody readCodeEntries readCodes readSections)
open Silmaril.Wasm.Binary.Packed renaming Cursor → PackedCursor

private theorem bind_at {α β : Type} {action : DecodeM α} {tail : α → DecodeM β}
    {start next : Cursor} {value : α} (success : action.run start = .ok (value, next)) :
    (action >>= tail).run start = (tail value).run next := by
  rw [StateT.run_bind, success]
  rfl

private theorem observe {α : Type} {reader : Reader α} {reference : DecodeM α}
    (agrees : Agrees id reader reference) {source : KBytes} {wf : source.wf = true}
    {pos : Nat} {value : α} {next : PackedCursor}
    (checked : reader.run ⟨source, wf, pos⟩ = .ok (value, next))
    (frame : Frame reference) (bound : pos ≤ source.len) :
    reference.run ⟨source.toByteArray, pos⟩ = .ok (value, ⟨source.toByteArray, next.pos⟩) := by
  have run := (agrees ⟨source, wf, pos⟩).symm.trans (congrArg (Except.map _) checked)
  change reference.run ⟨source.toByteArray, pos⟩ = .ok (value, next.spec) at run
  have same := (frame.self run (by change pos ≤ source.toList.length; rwa [source.length_toList wf])).1
  cases eq : next.spec with
  | mk bytes pos =>
    rw [eq] at same run
    have nextPos : next.pos = pos := congrArg Core.Decode.Cursor.pos eq
    change bytes = source.toByteArray at same
    subst bytes
    simpa only [nextPos] using run

private theorem slice_at {source : KBytes} {wf : source.wf = true} {pos size : Nat}
    (bound : pos + size ≤ source.len) : At source.toList pos (source.slice pos size).toList := by
  have length := (source.slice pos size).length_toList (source.wf_slice _ _ wf bound)
  rw [source.len_slice] at length
  constructor
  · rw [length, source.toList_slice _ _ wf bound]
  · rwa [length, source.length_toList wf]

private theorem codeEntries_sound {source : KBytes} {wf : source.wf = true}
    {ends : List Nat} {pos : Nat} {entries : List CodeEntry}
    (checked : readCodeEntries source ends pos = some entries) :
    (readVec.go readCode ends.length).run ⟨source.toByteArray, pos⟩ =
      .ok (entries, ⟨source.toByteArray, source.len⟩) := by
  induction ends generalizing pos entries with
  | nil =>
    simp only [readCodeEntries] at checked
    split at checked
    · rename_i endPos
      cases checked
      subst pos
      rfl
    · cases checked
  | cons stop ends ih =>
    simp only [readCodeEntries] at checked
    split at checked
    · rename_i guard
      split at checked
      · rename_i entry entryAt
        obtain ⟨rest, restAt, rfl⟩ := Option.map_eq_some_iff.1 checked
        have fit : pos + (stop - pos) ≤ source.len := by omega
        have entryRun := run_of_runAll frame_readCode entryAt (slice_at (wf := wf) fit)
        rw [(source.slice _ _).length_toList (source.wf_slice _ _ wf fit), source.len_slice,
          show pos + (stop - pos) = stop by omega] at entryRun
        have restRun := ih restAt
        change readCode.run ⟨source.toByteArray, pos⟩ =
          .ok (entry, ⟨source.toByteArray, stop⟩) at entryRun
        change (readCode >>= fun first => readVec.go readCode ends.length >>= fun more =>
          pure (first :: more)).run ⟨source.toByteArray, pos⟩ = _
        rw [bind_at entryRun, bind_at restRun]
        rfl
      · cases checked
    · cases checked

private theorem codes_sound {source : KBytes} {wf : source.wf = true} {ends : List Nat}
    {entries : List CodeEntry}
    (checked : readCodes source wf ends = some entries) :
    (readVec readCode).run ⟨source.toByteArray, 0⟩ = .ok (entries, ⟨source.toByteArray, source.len⟩) := by
  unfold readCodes at checked
  split at checked
  · rename_i count start countAt
    split at checked
    · rename_i fits
      have countRun := observe (readU_agrees 32) countAt (frame_readU 32) (Nat.zero_le _)
      change readU 32 ⟨arr source.toList, 0⟩ = .ok (count, ⟨arr source.toList, start.pos⟩) at countRun
      have countRun' := readCount_at (B := source.toList) (x := 0) (k := start.pos)
        (Nat.zero_add start.pos ▸ countRun)
        (by simpa only [Nat.zero_add, source.length_toList wf] using fits.2)
      rw [Nat.zero_add] at countRun'
      change readCount.run ⟨source.toByteArray, 0⟩ =
        .ok (count, ⟨source.toByteArray, start.pos⟩) at countRun'
      unfold readVec
      rw [bind_at countRun', fits.1]
      exact codeEntries_sound (wf := wf) checked
    · cases checked
  · cases checked

private theorem body_sound {id : Nat} {before after : Sections} {body : KBytes} {wf : body.wf = true}
    {codeEnds : Option (List Nat)}
    (checked : readBody id before body wf codeEnds = some after) :
    runAll (readSectionBody id before) body.toList = some after := by
  cases codeEnds with
  | none => exact checked
  | some _ =>
    simp only [readBody] at checked
    split at checked
    · rename_i isCode
      subst id
      obtain ⟨code, codeAt, rfl⟩ := Option.map_eq_some_iff.1 checked
      have parsed := body_code before _ _ _ (codes_sound codeAt)
      change (readSectionBody 10 before).run ⟨arr body.toList, 0⟩ =
        .ok ({ before with code }, ⟨body.toByteArray, body.len⟩) at parsed
      unfold runAll
      rw [parsed, body.length_toList wf]
      change (if body.len = body.len then _ else none) = _
      rw [ite_eq_left rfl]
    · exact checked

private theorem sections_sound {source : KBytes} {wf : source.wf = true}
    {codeEnds : Option (List Nat)} {fuel last pos : Nat} {initial result : Sections}
    (checked : readSections source wf codeEnds fuel pos last initial = some result) :
    (readModule.go fuel last initial).run ⟨source.toByteArray, pos⟩ =
      .ok (result, ⟨source.toByteArray, source.len⟩) := by
  induction fuel generalizing last pos initial with
  | zero =>
    simp only [readSections] at checked
    split at checked <;> rename_i endPos
    · cases checked; subst pos; rfl
    · cases checked
  | succ fuel ih =>
    simp only [readSections] at checked
    split at checked
    · rename_i endPos
      cases checked
      subst pos
      have len := source.length_toList wf
      have run := go_end (B := source.toList) (fuel := fuel) (last := last) (S := result)
      rw [len] at run
      exact run
    · split at checked
      · rename_i byte size start byteAt sizeAt
        split at checked
        · rename_i guard
          split at checked
          · rename_i next bodyAt
            have byteAt' : source.toList[pos]? = some byte := (source.get?_eq wf pos).symm.trans byteAt
            have within : pos + 1 ≤ source.len := by
              rw [← source.length_toList wf]
              have lt := (List.getElem?_eq_some_iff.1 byteAt').1
              omega
            have sizeAt' := observe (readU_agrees 32) sizeAt (frame_readU 32) within
            have sliceAt := slice_at (wf := wf) guard.2.2
            have bodyAt' := run_of_runAll (readSectionBody_frame _ _) (body_sound bodyAt) sliceAt
            rw [(source.slice start.pos size).length_toList
              (source.wf_slice _ _ wf guard.2.2), source.len_slice] at bodyAt'
            have step := go_known (fuel := fuel) byteAt' sizeAt'
              (by simpa only [source.length_toList wf] using guard.2.2) guard.1 guard.2.1 bodyAt'
            exact step.trans (ih checked)
          · cases checked
        · cases checked
      · cases checked

theorem sound {source : KBytes} {wf : source.wf = true} {codeEnds : Option (List Nat)}
    {decoded : Wasm.Module}
    (checked : Silmaril.Wasm.Binary.Packed.Bounded.decode? source wf codeEnds = some decoded) :
    Core.decode? source.toByteArray = some decoded := by
  unfold Silmaril.Wasm.Binary.Packed.Bounded.decode? at checked
  split at checked
  · rename_i head headAt
    split at checked
    · rename_i headPos
      have header := observe readHeader_agrees headAt readHeader_frame (Nat.zero_le _)
      rw [headPos] at header
      simp only [Option.bind_eq_some_iff] at checked
      obtain ⟨sections, ran, finished⟩ := checked
      have parsed := sections_sound ran
      have len : source.toByteArray.size = source.len := source.length_toList wf
      unfold finish at finished
      split at finished
      · rename_i guards
        simp only [Bool.and_eq_true] at guards
        cases finished
        have read : readModule.run ⟨source.toByteArray, 0⟩ =
            .ok (assemble sections, ⟨source.toByteArray, source.len⟩) := by
          unfold readModule
          rw [bind_at header, bind_at (show (get : DecodeM Cursor).run ⟨source.toByteArray, 8⟩ = .ok _ from rfl)]
          dsimp only
          rw [len, bind_at parsed, bind_at (show remaining.run ⟨source.toByteArray, source.len⟩ =
            .ok (source.toByteArray.size - source.len, ⟨source.toByteArray, source.len⟩) from rfl)]
          simp only [len, Nat.sub_self, beq_self_eq_true, ↓reduceIte, guards.1.1, guards.1.2, guards.2]
          rfl
        unfold Core.decode? decodeModule StateT.run'
        change (match (readModule.run ⟨source.toByteArray, 0⟩).map Prod.fst with
          | .ok result => some result | .error _ => none) = _
        rw [read]
        rfl
      · cases finished
    · cases checked
  · cases checked

end Silmaril.Proofs.Wasm.Binary.Packed.Bounded
