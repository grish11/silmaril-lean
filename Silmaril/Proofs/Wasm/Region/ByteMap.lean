module

public import Silmaril.Wasm.Region.ByteMap.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Proofs
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

 theorem parseAll_sound {α : Type} {G : Bytes → α → Prop} {parser : Decode.DecodeM α}
    (sound : Decode.Sound G parser) {bytes : Bytes} {a : α}
    (h : parseAll? parser bytes = some a) : G bytes a := by
  unfold parseAll? at h
  split at h
  · contradiction
  · rename_i result cursor run
    split at h
    · rename_i rest
      cases h
      obtain ⟨_, pre, hr, hg⟩ := sound run
      rw [rest, List.append_nil] at hr
      have eq : bytes = pre := by simpa [Decode.Cursor.rest] using hr
      simpa only [← eq] using hg
    · contradiction

 theorem readOne_sound (fuel : Nat) : Decode.Sound (Binary.Core.Instr Forms.all) (readOne fuel) := by
  intro c i c' h
  obtain ⟨op, cm, hop, hi⟩ := Decode.bindOk h
  obtain ⟨hb, pre, hr, hg⟩ := (Decode.readInstr_readSeq_sound fuel).1 op hi
  obtain ⟨hb₀, pre₀, hr₀, hg₀⟩ := Decode.readByte_sound hop
  cases hg₀
  exact ⟨hb.trans hb₀, [op] ++ pre, by simp [hr₀, hr], hg⟩

theorem expr_inversion {bytes : Bytes} {is : Silmaril.Wasm.Expr}
    (h : Binary.Core.Expr Forms.all bytes is) :
    ∃ b, bytes = b ++ [0x0B] ∧ Instrs Forms.all b is := by
  cases h with | mk encoded => exact ⟨_, rfl, encoded⟩

 theorem span_sound {input : Input} {m : ByteMapEntry} (h : input.SpanChecks m) :
    input.DecodesAt m.decoded m.bytes := by
  obtain ⟨hf, hp, start, _, _, prefixFact, existsI, instr⟩ := h
  have prefixFact := parseAll_sound Decode.readExpr_sound prefixFact
  have prefix' : Instrs Forms.all (input.prefixBytes m.bytes)
      (input.body.take m.decoded.instructionOffset) := by
    obtain ⟨b, eq, encoded⟩ := expr_inversion prefixFact
    have eq : input.prefixBytes m.bytes = b := List.append_cancel_right eq
    simpa only [← eq] using encoded
  cases hi : input.body[m.decoded.instructionOffset]? with
  | none => simp [hi] at existsI
  | some i =>
    exact ⟨hf, hp, start, prefix', i, hi,
      parseAll_sound (readOne_sound _) (by simpa [hi] using instr)⟩

 def certify (input : Input) (entries : List ByteMapEntry)
    (body : input.BodyChecks) (table : input.TableChecks entries) : Certified input := by
  obtain ⟨_, size, locals, expr⟩ := body
  have hl₀ := parseAll_sound (Decode.readVec_sound Decode.readLocals_sound) locals
  have hl := Decode.vec_map expandLocal (fun _ _ h => h) hl₀
  have he := parseAll_sound Decode.readExpr_sound expr
  refine ⟨hl, he, ?_, ⟨entries, ?_, ?_, table.2.1, table.2.2⟩⟩
  · simpa only [List.take_append_drop, List.flatMap_def] using Binary.Core.Func.mk hl he size
  · exact fun m hm => span_sound (table.1 m hm)
  · intro m hm
    exact ⟨(table.1 m hm).2.2.2.1, (table.1 m hm).2.2.2.2.1⟩

end Silmaril.Wasm.Region.ByteMap.Proofs
