module

public import Silmaril.Formats.Cbor.Value.Defs

public section

namespace Silmaril.Proofs.Formats.Cbor.Value

open Silmaril.Formats.Cbor

private theorem fold_bound (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun total byte => total * 256 + byte.toNat) acc < (acc + 1) * 256 ^ bytes.length := by
  induction bytes generalizing acc with
  | nil => simp
  | cons byte tail ih =>
    have bound := byte.toNat_lt
    calc
      _ < (acc * 256 + byte.toNat + 1) * 256 ^ tail.length := ih _
      _ ≤ _ := by
        simp only [List.length_cons, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (256 ^ tail.length) 256]
        exact Nat.mul_le_mul_right _ (by omega)

private theorem readArg_bound {ai amount : Nat} {bytes rest : List UInt8}
    (read : readArg ai bytes = some (amount, rest)) :
    amount < 2 ^ 64 ∧ (24 ≤ ai → amount < 256 ^ (if ai = 24 then 1 else aiWidth ai)) := by
  unfold readArg at read
  split at read
  · rename_i small
    cases Option.some.inj read
    exact ⟨by omega, by omega⟩
  · split at read
    · rename_i width hwidth
      split at read
      · cases Option.some.inj read
        have small := fold_bound (bytes.take width) 0
        change beNat (bytes.take width) < (0 + 1) * 256 ^ (bytes.take width).length at small
        simp only [Nat.zero_add, Nat.one_mul, List.length_take] at small
        have power := Nat.pow_le_pow_right (by decide : 0 < 256) (Nat.min_le_left width bytes.length)
        have bound := Nat.lt_of_lt_of_le small power
        by_cases one : ai = 24
        · subst ai; change some 1 = some width at hwidth
          cases Option.some.inj hwidth
          simp at bound ⊢
          omega
        by_cases two : ai = 25
        · subst ai; change some 2 = some width at hwidth
          cases Option.some.inj hwidth
          simp [aiWidth] at bound ⊢
          omega
        by_cases four : ai = 26
        · subst ai; change some 4 = some width at hwidth
          cases Option.some.inj hwidth
          simp [aiWidth] at bound ⊢
          omega
        by_cases eight : ai = 27
        · subst ai; change some 8 = some width at hwidth
          cases Option.some.inj hwidth
          simp [aiWidth] at bound ⊢
          omega
        simp [argWidth] at hwidth
      · contradiction
    · contradiction

mutual

private theorem item_encodable (fuel : Nat) (bytes : List UInt8) (value : Value) (rest : List UInt8)
    (read : decodeItem fuel bytes = some (value, rest)) : value.Encodable := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    cases bytes with
    | nil => contradiction
    | cons byte tail =>
      simp only [decodeItem] at read
      split at read
      · contradiction
      split at read
      · split at read
        · cases Option.some.inj read; exact Or.inl (by assumption)
        obtain ⟨⟨argument, suffix⟩, arg, result⟩ := Option.bind_eq_some_iff.mp read
        split at result
        · split at result
          · cases Option.some.inj result
            have cap := (readArg_bound arg).2 (by omega)
            exact Or.inr ⟨by assumption, by simpa [‹byte.toNat % 32 = 24›] using cap⟩
          · contradiction
        · cases Option.some.inj result
          have cap := (readArg_bound arg).2 (by omega)
          refine ⟨?_, by simpa [‹byte.toNat % 32 ≠ 24›] using cap⟩
          by_cases half : byte.toNat % 32 = 25
          · simp [aiWidth, half]
          by_cases single : byte.toNat % 32 = 26
          · simp [aiWidth, single]
          have double : byte.toNat % 32 = 27 := by omega
          simp [aiWidth, double]
      · obtain ⟨⟨argument, suffix⟩, arg, result⟩ := Option.bind_eq_some_iff.mp read
        have cap := (readArg_bound arg).1
        split at result
        · cases Option.some.inj result; exact cap
        split at result
        · cases Option.some.inj result; exact cap
        split at result
        · split at result
          · cases Option.some.inj result; simp [Value.Encodable]; omega
          · contradiction
        split at result
        · split at result
          · cases Option.some.inj result; simp [Value.Encodable]; omega
          · contradiction
        split at result
        · obtain ⟨⟨items, afterItems⟩, decoded, same⟩ := Option.map_eq_some_iff.mp result
          cases same
          obtain ⟨count, children⟩ := list_encodable fuel argument suffix items afterItems decoded
          exact ⟨count ▸ cap, children⟩
        split at result
        · obtain ⟨⟨entries, afterEntries⟩, decoded, same⟩ := Option.map_eq_some_iff.mp result
          cases same
          obtain ⟨count, children⟩ := map_encodable fuel argument suffix entries afterEntries decoded
          exact ⟨count ▸ cap, children⟩
        · obtain ⟨⟨content, afterContent⟩, decoded, same⟩ := Option.map_eq_some_iff.mp result
          cases same
          exact ⟨cap, item_encodable fuel suffix content afterContent decoded⟩

private theorem list_encodable (fuel count : Nat) (bytes : List UInt8) (items : List Value)
    (rest : List UInt8) (read : decodeList fuel count bytes = some (items, rest)) :
    items.length = count ∧ ListEncodable items := by
  cases count with
  | zero => simp [decodeList] at read; obtain ⟨rfl, _⟩ := read; exact ⟨rfl, trivial⟩
  | succ count =>
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      obtain ⟨⟨head, next⟩, headRead, tailRead⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨⟨tail, afterTail⟩, decoded, same⟩ := Option.map_eq_some_iff.mp tailRead
      cases same
      obtain ⟨length, children⟩ := list_encodable fuel count next tail afterTail decoded
      exact ⟨congrArg Nat.succ length, item_encodable fuel bytes head next headRead, children⟩

private theorem map_encodable (fuel count : Nat) (bytes : List UInt8) (entries : List (Value × Value))
    (rest : List UInt8) (read : decodeMap fuel count bytes = some (entries, rest)) :
    entries.length = count ∧ MapEncodable entries := by
  cases count with
  | zero => simp [decodeMap] at read; obtain ⟨rfl, _⟩ := read; exact ⟨rfl, trivial⟩
  | succ count =>
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      obtain ⟨⟨key, afterKey⟩, keyRead, remainder⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨⟨value, afterValue⟩, valueRead, tailRead⟩ := Option.bind_eq_some_iff.mp remainder
      obtain ⟨⟨tail, afterTail⟩, decoded, same⟩ := Option.map_eq_some_iff.mp tailRead
      cases same
      obtain ⟨length, children⟩ := map_encodable fuel count afterValue tail afterTail decoded
      exact ⟨congrArg Nat.succ length, item_encodable fuel bytes key afterKey keyRead,
        item_encodable fuel afterKey value afterValue valueRead, children⟩

end

theorem encodable_of_decode {bytes : List UInt8} {value : Value}
    (read : decode bytes = some value) : value.Encodable := by
  unfold decode at read
  split at read
  · cases Option.some.inj read
    exact item_encodable _ _ _ _ (by assumption)
  · contradiction

end Silmaril.Proofs.Formats.Cbor.Value
