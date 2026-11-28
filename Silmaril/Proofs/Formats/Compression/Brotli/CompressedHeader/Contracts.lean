module

public import Silmaril.Formats.Compression.Brotli.CompressedHeader.Defs
import Silmaril.Formats.Compression.Brotli.ContextHeader.Thms
import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Thms
import Silmaril.Formats.Compression.Brotli.BlockTypes.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.CompressedHeader

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.CompressedHeader
open Silmaril.Formats.Compression.Brotli.CompressedHeader.Internal
open Huffman.Description (Table)

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.trans {before middle after : Cursor} {input a rest b suffix : List Bool}
    (first : Advance before middle input a rest) (second : Advance middle after rest b suffix) :
    Advance before after input (a ++ b) suffix := by
  refine ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.count, ?_, ?_⟩
  · simp only [List.length_append, first.offset, second.offset]
    omega
  · simp only [List.length_append, first.budget, second.budget]
    omega

private theorem advanced {before : Cursor} {after : LSBReader} {input used suffix : List Bool}
    (split : input = used ++ suffix) (rep : after.Rep suffix) (count : after.count < 8)
    (offset : after.totalRead = before.reader.totalRead + used.length) (cap : used.length ≤ before.remaining) :
    Advance before (before.advance after) input used suffix :=
  ⟨split, rep, count, offset, by simp only [Cursor.advance, offset]; omega⟩

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {ε α : Type} {action : Except ε α} {f : ε → Error} {value : α}
    (read : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases read <;> rfl

private theorem readMap_sound {kind : ContextMap.Kind} {types : Nat}
    {before after : Cursor} {input : List Bool} {map : ContextMap.Decode.Map}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readMap kind types before = .ok (map, after)) :
    ∃ work used suffix, work ≤ kind.extent types ∧ ContextMap.Decode.Wire (kind.extent types) work used map ∧
      Advance before after input used suffix := by
  unfold readMap at read
  obtain ⟨⟨output, cursor⟩, actual, done⟩ := bind_ok read
  cases done
  obtain ⟨_, _, _, work, used, suffix, bound, wire, split, rep', count', offset, cap⟩ :=
    ContextMap.Decode.read_sound rep count (mapError_ok actual)
  exact ⟨work, used, suffix, bound, wire, advanced split rep' count' offset cap⟩

private theorem readGroup_sound {group : Group} {alphabet count ordinal : Nat}
    {before after : Cursor} {input : List Bool} {tables : List Table}
    (rep : before.reader.Rep input) (byteBound : before.reader.count < 8)
    (read : readGroup group alphabet count ordinal before = .ok (tables, after)) :
    ∃ used suffix, GroupWire alphabet count used tables ∧ Advance before after input used suffix := by
  induction count generalizing ordinal before after input tables with
  | zero =>
    cases read
    exact ⟨[], input, .done, ⟨by simp, rep, byteBound, by simp, by simp⟩⟩
  | succ count ih =>
    unfold readGroup at read
    obtain ⟨⟨table, cursor⟩, tableRead, read⟩ := bind_ok read
    obtain ⟨⟨tail, final⟩, tailRead, done⟩ := bind_ok read
    cases done
    obtain ⟨_, _, _, size, used, middle, wire, split, rep', count', offset, cap, _⟩ :=
      Huffman.Description.read_sound rep byteBound (mapError_ok tableRead)
    have first := advanced split rep' count' offset (show used.length ≤ before.remaining from cap)
    obtain ⟨tailBits, suffix, tailWire, second⟩ := ih first.rep first.count tailRead
    exact ⟨_, suffix, .next wire size tailWire, first.trans second⟩

theorem GroupWire.valid {alphabet count : Nat} {bits : List Bool} {tables : List Table}
    (wire : GroupWire alphabet count bits tables) :
    tables.length = count ∧ ∀ table ∈ tables, table.alphabetSize = alphabet := by
  induction wire with
  | done => simp
  | next _ size _ ih => simpa [ih.1, size] using ih.2

theorem Wire.groups {work : Nat} {bits : List Bool} {header : Header} (wire : Wire work bits header) :
    ∀ group, (header.tables group).length = group.count header.initial header.literalMap header.distanceMap ∧
      ∀ table ∈ header.tables group, table.alphabetSize = group.alphabet header.initial.fields := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, literal, insertCopy, distance⟩ := wire.parts
  intro group
  cases group
  · exact GroupWire.valid literal
  · exact GroupWire.valid insertCopy
  · exact GroupWire.valid distance

theorem Wire.bounds {work : Nat} {bits : List Bool} {header : Header} (wire : Wire work bits header) :
    work ≤ header.mapEntries ∧ header.mapEntries ≤ 17408 ∧ 3 ≤ header.treeCount ∧ header.treeCount ≤ 768 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, initial, literal, distance, litTrees, insTrees, distTrees⟩ := wire.parts
  obtain ⟨_, _, _, controls, _⟩ := initial
  obtain ⟨_, _, _, _, l, i, d⟩ := controls
  have lType := BlockTypes.ControlWire.bounds l
  have iType := BlockTypes.ControlWire.bounds i
  have dType := BlockTypes.ControlWire.bounds d
  have lMap := ContextMap.Decode.Wire.valid literal
  have dMap := ContextMap.Decode.Wire.valid distance
  have lCount := (GroupWire.valid litTrees).1
  have iCount := (GroupWire.valid insTrees).1
  have dCount := (GroupWire.valid distTrees).1
  have lWork := lMap.2.1
  have dWork := dMap.2.1
  have lMin := lMap.2.2.1
  have lMax := lMap.2.2.2.1
  have dMin := dMap.2.2.1
  have dMax := dMap.2.2.2.1
  simp only [Header.treeCount, Header.mapEntries, mapExtent, ContextMap.Kind.extent, ContextMap.Kind.contexts]
    at lWork dWork ⊢
  omega

theorem read_sound {limits : Limits} {before after : LSBReader} {input : List Bool} {header : Header}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.CompressedHeader.read limits before = .ok (header, after)) :
    header.mapEntries ≤ limits.mapEntries ∧ header.treeCount ≤ limits.trees ∧
    ∃ work used suffix, work ≤ limits.mapEntries ∧ Wire work used header ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits := by
  unfold Silmaril.Formats.Compression.Brotli.CompressedHeader.read at read
  obtain ⟨⟨initial, afterInitial⟩, initialRead, next⟩ := bind_ok read
  simp only [] at next
  split at next <;> try contradiction
  rename_i entryCap
  obtain ⟨⟨literal, afterLiteral⟩, literalRead, next⟩ := bind_ok next
  obtain ⟨⟨distance, afterDistance⟩, distanceRead, next⟩ := bind_ok next
  simp only [] at next
  split at next <;> try contradiction
  rename_i treeCap
  obtain ⟨⟨literalTrees, afterLitTrees⟩, literalTreesRead, next⟩ := bind_ok next
  obtain ⟨⟨insertTrees, afterInsertTrees⟩, insertTreesRead, next⟩ := bind_ok next
  obtain ⟨⟨distanceTrees, final⟩, distanceTreesRead, done⟩ := bind_ok next
  cases done
  obtain ⟨a, rest, _, initialWire, split, rep', count', _, _, offset, cap⟩ :=
    ContextHeader.read_sound rep count (mapError_ok initialRead)
  have first := advanced (before := ⟨before, limits.bits⟩) split rep' count' offset cap
  obtain ⟨lw, b, _, lwCap, literalWire, second⟩ := readMap_sound first.rep first.count literalRead
  obtain ⟨dw, c, _, dwCap, distanceWire, third⟩ := readMap_sound second.rep second.count distanceRead
  obtain ⟨d, _, literalGroup, fourth⟩ := readGroup_sound third.rep third.count literalTreesRead
  obtain ⟨e, _, insertGroup, fifth⟩ := readGroup_sound fourth.rep fourth.count insertTreesRead
  obtain ⟨f, suffix, distanceGroup, sixth⟩ := readGroup_sound fifth.rep fifth.count distanceTreesRead
  have total := ((((first.trans second).trans third).trans fourth).trans fifth).trans sixth
  have budget := total.budget
  have lCount := (GroupWire.valid literalGroup).1
  have iCount := (GroupWire.valid insertGroup).1
  have dCount := (GroupWire.valid distanceGroup).1
  change _ ≤ limits.mapEntries ∧ _ ≤ limits.trees ∧ _
  simp only [Header.mapEntries, Header.treeCount]
  rw [lCount, iCount, dCount]
  refine ⟨by omega, by omega, lw + dw, _, suffix, ?_, ?_,
    total.split, total.rep, total.count, total.offset, ?_⟩
  · simp only [mapExtent] at entryCap
    omega
  · exact ⟨a, b, c, d, e, f, lw, dw, rfl, rfl, initialWire,
      literalWire, distanceWire, literalGroup, insertGroup, distanceGroup⟩
  · dsimp at budget
    omega

end Silmaril.Proofs.Formats.Compression.Brotli.CompressedHeader
