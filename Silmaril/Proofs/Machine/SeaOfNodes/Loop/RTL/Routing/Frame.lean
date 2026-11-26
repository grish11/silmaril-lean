module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.RVSDG (Port Tuple)

private theorem prefix_index {pre tail : List PortTy} {t : PortTy} (p : Port pre t) :
    (prefixPort (tail := tail) p).index = p.index := by
  induction p with
  | head => rfl
  | tail _ ih => simp [prefixPort, Port.index, ih]

theorem suffix_index {tail : List PortTy} {t : PortTy} (pre : List PortTy) (p : Port tail t) :
    (suffixPort pre p).index = pre.length + p.index := by
  induction pre with
  | nil => simp [suffixPort]
  | cons head rest ih =>
    simp only [suffixPort, Port.index, List.length_cons, ih]
    omega

private theorem prefix_get {pre tail : List PortTy} {t : PortTy} (p : Port pre t)
    (left : Tuple (Val model.value) pre) (right : Tuple (Val model.value) tail) :
    (appendTuple right left).get (prefixPort p) = left.get p := by
  induction p with
  | head => cases left; rfl
  | tail p ih =>
    cases left with
    | cons _ rest => exact ih rest

theorem suffix_get {F : PortTy → Type*} {pre tail : List PortTy} {t : PortTy}
    (left : Tuple F pre) (right : Tuple F tail) (p : Port tail t) :
    (appendTuple right left).get (suffixPort pre p) = right.get p := by
  induction left with
  | nil => rfl
  | cons _ rest ih => exact ih

private theorem split_port {pre tail : List PortTy} {t : PortTy} (p : Port (pre ++ tail) t) :
    (∃ q : Port pre t, p = prefixPort q) ∨ (∃ q : Port tail t, p = suffixPort pre q) := by
  induction pre with
  | nil => exact .inr ⟨p, rfl⟩
  | cons head rest ih =>
    cases p with
    | head => exact .inl ⟨.head, rfl⟩
    | tail p =>
      rcases ih p with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · exact .inl ⟨.tail q, rfl⟩
      · exact .inr ⟨q, rfl⟩

private theorem index_lt {ts : List PortTy} {t : PortTy} (p : Port ts t) : p.index < ts.length := by
  induction p with
  | head => simp [Port.index]
  | tail _ ih => simpa [Port.index] using Nat.succ_lt_succ ih

theorem wordPorts_length (n : Nat) : (wordPorts n).length = n := by
  simp

theorem bindWords_write {arity : Nat} (base : Nat) (fr : Frame Reg) (values : WordTuple arity) :
    fr.writeAll (paramRegs base arity) (words values) = some (bindWords base fr values) := by
  induction arity generalizing base fr with
  | zero => cases values; rfl
  | succ arity ih =>
    cases values with
    | cons head tail =>
      simpa only [paramRegs, List.range'_succ, List.map_cons, words, Frame.writeAll, bindWords,
        Nat.add_one] using ih (base + 1) (fr.set (.arg base) head) tail

private theorem bindWords_before {arity : Nat} (base : Nat) (fr : Frame Reg) (values : WordTuple arity)
    (i : Nat) (before : i < base) :
    (bindWords base fr values).get (.arg i) = fr.get (.arg i) := by
  induction arity generalizing base fr with
  | zero => cases values; rfl
  | succ arity ih =>
    cases values with
    | cons head tail =>
      change (bindWords (base + 1) (fr.set (.arg base) head) tail).get _ = _
      rw [ih _ _ tail (by omega)]
      have preserve (value : Word) : (fr.set (.arg base) value).get (.arg i) = fr.get (.arg i) := by
        simp [show i ≠ base by omega]
      exact preserve head

theorem bindWords_get {arity : Nat} (base : Nat) (fr : Frame Reg) (values : WordTuple arity)
    (p : Port (wordPorts arity) wordPort) :
    (bindWords base fr values).get (.arg (base + p.index)) = some (values.get p) := by
  induction arity generalizing base fr with
  | zero => nomatch p
  | succ arity ih =>
    cases values with
    | cons head tail =>
      cases p with
      | head =>
        change (bindWords (base + 1) (fr.set (.arg base) head) tail).get (.arg base) = some head
        rw [bindWords_before _ _ _ _ (by omega)]
        have written (value : Word) : (fr.set (.arg base) value).get (.arg base) = some value := by simp
        exact written head
      | tail p =>
        change (bindWords (base + 1) (fr.set (.arg base) head) tail).get
          (.arg (base + (p.index + 1))) = some (tail.get p)
        rw [show base + (p.index + 1) = base + 1 + p.index by omega]
        exact ih _ _ tail p

theorem bank_matches_at {arity : Nat} {fr : Frame Reg} {input : WordTuple arity}
    (agree : ArgsMatch fr input) (values : WordTuple arity) :
    ArgsMatch (bindWords arity fr values) (appendTuple values input) := by
  intro p
  rcases split_port p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [prefix_index, prefix_get]
    have before : q.index < arity := by simpa only [wordPorts_length] using index_lt q
    exact (bindWords_before _ _ _ _ before).trans (agree q)
  · rw [suffix_index, suffix_get, wordPorts_length]
    exact bindWords_get _ _ _ q

theorem input_matches_at {arity : Nat} {fr : Frame Reg} {input old : WordTuple arity}
    (agree : ArgsMatch fr (appendTuple old input)) : ArgsMatch fr input := by
  intro p
  simpa only [prefix_index, prefix_get] using agree (prefixPort p)

theorem bank_matches {payloads : Nat} {fr : Frame Reg} {input : WordTuple (payloads + 1)}
    (agree : ArgsMatch fr input) (values : WordTuple (payloads + 1)) :
    ArgsMatch (bindBank fr values) (appendTuple values input) :=
  bank_matches_at agree values

theorem input_matches {payloads : Nat} {fr : Frame Reg} {input old : WordTuple (payloads + 1)}
    (agree : ArgsMatch fr (appendTuple old input)) : ArgsMatch fr input :=
  input_matches_at agree

theorem bindWords_args {arity : Nat} (values : WordTuple arity) :
    ArgsMatch (bindWords 0 Frame.empty values) values := by
  intro p
  simpa only [Nat.zero_add] using bindWords_get 0 Frame.empty values p

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
