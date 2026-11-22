module

public import Silmaril.Crypto.Blake3.Range.EOF.Defs
public import Silmaril.Crypto.Blake3.Range.Thms
import Silmaril.Proofs.Crypto.Blake3.Words
import Init.Data.List.TakeDrop

public section

namespace Silmaril.Proofs.Crypto.Blake3

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice)

private theorem input_or_collision {rel : Compression} {left right : Input} {output : CV}
    (lhs : rel left output) (rhs : rel right output) : left = right ∨ Compression.Collision rel :=
  if eq : left = right then .inl eq else .inr ⟨left, right, output, eq, lhs, rhs⟩

private theorem first_eq {root last first second : Bool} {left right : Nat} {lcv rcv : CV} {lhs rhs : Bytes}
    (eq : chunkInput root first last left lcv lhs = chunkInput root second last right rcv rhs) :
    first = second := by
  have flags := congrArg Input.flags eq
  cases root <;> cases last <;> cases first <;> cases second <;> simp_all [chunkInput]

private theorem parent_ne_final {root first : Bool} {left right cv : CV} {chunk : Nat} {bytes : Bytes} :
    parentInput root left right ≠ chunkInput root first true chunk cv bytes := by
  intro eq
  have flags := congrArg Input.flags eq
  cases root <;> cases first <;> simp_all [parentInput, chunkInput]

/-- Non-final compression steps in reverse order of inspection, anchored at the chunk IV. -/
private inductive Prefix (rel : Compression) (chunk : Nat) : Nat → CV → Prop where
  | empty : Prefix rel chunk 0 iv
  | push {count cv output bytes} : Prefix rel chunk count cv →
      rel (chunkInput false (count == 0) false chunk cv bytes) output → Prefix rel chunk (count + 1) output

private theorem Prefix.countOrCollision {rel : Compression} {left right before after : Nat} {output : CV}
    (lhs : Prefix rel left before output) (rhs : Prefix rel right after output)
    (first : (before == 0) = (after == 0)) : before = after ∨ Compression.Collision rel := by
  induction lhs generalizing after with
  | empty =>
    have zero : after = 0 := by simpa using first
    exact .inl zero.symm
  | push prev hit ih =>
    cases rhs with
    | empty => simp at first
    | push rprev rhit =>
      rcases input_or_collision hit rhit with eq | collision
      · have cv := congrArg Input.cv eq
        cases cv
        exact (ih rprev (first_eq eq)).imp (congrArg (· + 1)) id
      · exact .inr collision

private theorem chain_final {rel : Compression} {root first : Bool} {chunk more before : Nat}
    {cv output : CV} {bytes : Bytes} (chain : Chain rel root chunk more first cv bytes output)
    (prevSteps : Prefix rel chunk before cv) (start : first = (before == 0)) :
    ∃ prior tail, Prefix rel chunk (before + more) prior ∧ tail.length ≤ 64 ∧
      bytes.length = 64 * more + tail.length ∧
      rel (chunkInput root (before + more == 0) true chunk prior tail) output := by
  induction chain generalizing before with
  | last bound hit =>
    rw [start] at hit
    exact ⟨_, _, by simpa using prevSteps, bound, by simp, by simpa using hit⟩
  | @step remaining began state rest mid out large hit _ ih =>
    obtain ⟨prior, tail, prev, bound, len, last⟩ :=
      ih (Prefix.push prevSteps (start ▸ hit)) (by simp : false = (before + 1 == 0))
    have count : before + 1 + remaining = before + (remaining + 1) := by omega
    simp only [List.length_drop] at len
    exact ⟨prior, tail, count ▸ prev, bound, by omega, count ▸ last⟩

/-- The part of a trace needed for EOF. The index is the absolute byte end, not a supplied
length field. Each fork retains the actual parent input and only the right child's trace. -/
private inductive EndTrace (rel : Compression) : Bool → Nat → CV → Prop where
  | leaf {root chunk more bytes output} : validSize chunk → (root = true → chunk = 0) →
      Chain rel root chunk more true iv bytes output → EndTrace rel root (1024 * chunk + bytes.length) output
  | fork {root extent left right output} : EndTrace rel false extent right →
      rel (parentInput root left right) output → EndTrace rel root extent output

private theorem trace_end {rel : Compression} {root : Bool} {first size : Nat} {opening : Opening} {output : CV}
    (trace : Trace rel root (geometry first size) opening output) (edge : opening.exposesEOF = true)
    (rootIndex : root = true → first = 0) : EndTrace rel root (1024 * first + size) output := by
  induction size using Nat.strongRecOn generalizing first root opening output with
  | ind size ih =>
    rw [geometry] at trace
    split at trace
    · cases trace with
      | «opaque» => simp [Opening.exposesEOF] at edge
      | leaf ok chain => exact ok.1 ▸ EndTrace.leaf ok.2.2 rootIndex chain
    · rename_i large
      have pos : 0 < splitBytes size := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      have powBound := Nat.mul_le_mul_left 1024 (Nat.log2_self_le (n := (size - 1) / 1024) (by omega))
      have lt : splitBytes size < size := by unfold splitBytes; omega
      have aligned : 1024 * (splitBytes size / 1024) = splitBytes size := by simp [splitBytes]
      cases trace with
      | «opaque» => simp [Opening.exposesEOF] at edge
      | fork _ right hit =>
        have extent : 1024 * (first + splitBytes size / 1024) + (size - splitBytes size) =
            1024 * first + size := by rw [Nat.mul_add, aligned]; omega
        exact extent ▸ EndTrace.fork (ih _ (by omega) right edge (by simp)) hit

private theorem leaf_extent_or_collision {rel : Compression} {root : Bool} {left right before after : Nat}
    {lhs rhs : Bytes} {output : CV} (leftBound : validSize left) (rightBound : validSize right)
    (leftRoot : root = true → left = 0) (rightRoot : root = true → right = 0)
    (lchain : Chain rel root left before true iv lhs output) (rchain : Chain rel root right after true iv rhs output) :
    1024 * left + lhs.length = 1024 * right + rhs.length ∨ Compression.Collision rel := by
  obtain ⟨lcv, ltail, lprefix, lbound, llen, lhit⟩ := chain_final lchain .empty rfl
  obtain ⟨rcv, rtail, rprefix, rbound, rlen, rhit⟩ := chain_final rchain .empty rfl
  simp only [Nat.zero_add] at lprefix rprefix lhit rhit
  rcases input_or_collision lhit rhit with eq | collision
  · have sameChunk : left = right := by
      cases root
      · have ctr := congrArg (UInt64.toNat ∘ Input.counter) eq
        change (UInt64.ofNat left).toNat = (UInt64.ofNat right).toNat at ctr
        simpa only [UInt64.toNat_ofNat_of_lt' leftBound, UInt64.toNat_ofNat_of_lt' rightBound] using ctr
      · exact (leftRoot rfl).trans (rightRoot rfl).symm
    have sameLen : ltail.length = rtail.length := by
      have len := congrArg (UInt32.toNat ∘ Input.blockLen) eq
      change (UInt32.ofNat ltail.length).toNat = (UInt32.ofNat rtail.length).toNat at len
      have small : 64 < UInt32.size := by decide
      simpa only [UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt lbound small),
        UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt rbound small)] using len
    have cv := congrArg Input.cv eq
    cases cv
    exact (lprefix.countOrCollision rprefix (first_eq eq)).imp (fun count => by omega) id
  · exact .inr collision

private theorem EndTrace.extentOrCollision {rel : Compression} {root : Bool} {left right : Nat} {output : CV}
    (lhs : EndTrace rel root left output) (rhs : EndTrace rel root right output) :
    left = right ∨ Compression.Collision rel := by
  induction lhs generalizing right with
  | leaf lbound lroot lchain =>
    cases rhs with
    | leaf rbound rroot rchain => exact leaf_extent_or_collision lbound rbound lroot rroot lchain rchain
    | fork _ rhit =>
      obtain ⟨_, _, _, _, _, lhit⟩ := chain_final lchain .empty rfl
      exact .inr ⟨_, _, _, Ne.symm parent_ne_final, lhit, rhit⟩
  | fork _ lhit ih =>
    cases rhs with
    | leaf _ _ rchain =>
      obtain ⟨_, _, _, _, _, rhit⟩ := chain_final rchain .empty rfl
      exact .inr ⟨_, _, _, parent_ne_final, lhit, rhit⟩
    | fork rtrace rhit =>
      rcases input_or_collision lhit rhit with eq | collision
      · obtain ⟨_, req⟩ := parent_inj eq
        cases req
        exact ih rtrace
      · exact .inr collision

theorem root_extent_or_collision {rel : Compression} {left right : Nat} {digest : Bytes} {lhs rhs : Opening}
    (lh : Root rel left digest lhs) (le : lhs.exposesEOF = true)
    (rh : Root rel right digest rhs) (re : rhs.exposesEOF = true) : left = right ∨ Compression.Collision rel := by
  obtain ⟨_, lcv, ltrace, leq⟩ := lh
  obtain ⟨_, rcv, rtrace, req⟩ := rh
  have eq := digest_inj (leq.trans req.symm)
  subst rcv
  simpa only [Nat.mul_zero, Nat.zero_add] using
    (trace_end ltrace le (fun _ => rfl)).extentOrCollision (trace_end rtrace re (fun _ => rfl))

theorem disclose_exposesEOF (shape : Shape) (bytes : Bytes) : (disclose shape bytes).exposesEOF = true := by
  induction shape generalizing bytes with
  | leaf => rfl
  | fork _ _ _ ih => exact ih _

private theorem disclosed_eq {shape : Shape} {left right : Bytes}
    (agree : Agree (disclose shape left) (disclose shape right)) : left = right := by
  induction shape generalizing left right with
  | leaf => cases agree; rfl
  | fork lshape _ leftIH rightIH =>
    cases agree with
    | fork lhs rhs =>
      rw [← List.take_append_drop lshape.size left, ← List.take_append_drop lshape.size right, leftIH lhs, rightIH rhs]

theorem named_eq_or_collision {rel : Compression} {digest left right : Bytes}
    (lh : Named rel digest left) (rh : Named rel digest right) : left = right ∨ Compression.Collision rel := by
  rcases root_extent_or_collision lh (disclose_exposesEOF _ _) rh (disclose_exposesEOF _ _) with eq | collision
  · have rhs : Root rel left.length digest (disclose (geometry 0 left.length) right) := by
      change Root rel right.length digest (disclose (geometry 0 right.length) right) at rh
      simpa only [← eq] using rh
    exact (lh.agreeOrCollision rhs).imp disclosed_eq id
  · exact .inr collision

end Silmaril.Proofs.Crypto.Blake3
