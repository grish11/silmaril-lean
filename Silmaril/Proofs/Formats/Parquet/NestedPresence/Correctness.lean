module

public import Silmaril.Formats.Parquet.NestedPresence.Defs
import all Silmaril.Formats.Parquet.NestedPresence.Defs
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.NestedPresence

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.NestedPresence

public theorem classify_contract {child : Child} {level : Nat} (h : level ≤ child.maxDefinition) :
    (classify child level = .parentAbsent ↔ level = 0) ∧
    (classify child level = .childNull ↔ child = .optional ∧ level = 1) ∧
    (classify child level = .value ↔ level = child.maxDefinition) := by
  cases child with
  | required =>
    change level ≤ 1 at h
    have cases' : level = 0 ∨ level = 1 := by omega
    rcases cases' with rfl | rfl <;> decide
  | optional =>
    change level ≤ 2 at h
    have cases' : level = 0 ∨ level = 1 ∨ level = 2 := by omega
    rcases cases' with rfl | rfl | rfl <;> decide

public theorem decode_wire {child : Child} {slots : Nat} {limits : Limits} {body : Bytes}
    {result : Result} (h : decode child slots limits body = .ok result) :
    Wire child slots limits body result := by
  unfold decode at h
  split at h
  · cases h
  rename_i cap
  cases splitBody : FlatPage.splitV1Optional limits.levels.bytes body with
  | error reason => simp [splitBody, Except.mapError, bind, Except.bind] at h
  | ok sections =>
    simp only [splitBody, Except.mapError, bind, Except.bind] at h
    cases decoded : Hybrid.decode child.width slots limits.levels sections.definitions with
    | error reason => simp [decoded] at h
    | ok levels =>
      simp only [decoded] at h
      split at h
      · cases h
      rename_i checked
      obtain rfl := Except.ok.inj h
      have levelOk : levels.all (fun level => decide (level ≤ child.maxDefinition)) = true := by
        cases eq : levels.all (fun level => decide (level ≤ child.maxDefinition)) <;> simp_all
      obtain ⟨word, length, size, byteCap, source⟩ := FlatPage.splitV1Optional_ok_iff.mp splitBody
      exact ⟨Nat.le_of_not_gt cap, by simp [Hybrid.decode_length decoded],
        word, sections.definitions, levels, length, size, byteCap, source,
        (Hybrid.decode_ok_iff.mp decoded).2.2.2.2,
        fun level mem => of_decide_eq_true (List.all_eq_true.mp levelOk level mem), rfl⟩

public theorem decodeV1_wire {child : Child} {limits : Limits} {header : Page.Header} {body : Bytes}
    {result : Result} (h : decodeV1 child limits header body = .ok result) : PageWire child limits header body result := by
  unfold decodeV1 at h
  split at h
  · rename_i info kind
    split at h
    · cases h
    rename_i crc
    split at h
    · cases h
    rename_i encoding
    split at h
    · cases h
    rename_i sizes
    have extent := not_not.mp sizes
    have tags := not_not.mp encoding
    exact ⟨by cases eq : header.crc <;> simp_all, extent.1, extent.2,
      info, kind, tags.1, tags.2.1, tags.2.2, decode_wire h⟩
  · cases h

end Silmaril.Proofs.Formats.Parquet.NestedPresence
