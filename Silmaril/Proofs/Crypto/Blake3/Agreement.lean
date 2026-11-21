module

public import Silmaril.Crypto.Blake3.Range.Defs
import Silmaril.Proofs.Crypto.Blake3.Words
import Init.Data.List.TakeDrop

public section

namespace Silmaril.Proofs.Crypto.Blake3

open Silmaril.Crypto.Blake3

private theorem input_or_collision {rel : Compression} {left right : Input} {output : CV}
    (lhs : rel left output) (rhs : rel right output) : left = right ∨ Compression.Collision rel :=
  if eq : left = right then .inl eq else .inr ⟨left, right, output, eq, lhs, rhs⟩

private theorem chain_agree {rel : Compression} {root first : Bool} {chunk more : Nat}
    {lcv rcv output : CV} {left right : Bytes} (len : left.length = right.length)
    (lhs : Chain rel root chunk more first lcv left output) (rhs : Chain rel root chunk more first rcv right output) :
    (left = right ∧ lcv = rcv) ∨ Compression.Collision rel := by
  induction more generalizing first lcv rcv output left right with
  | zero =>
    cases lhs with
    | last bound lhit =>
      cases rhs with
      | last _ rhit =>
        rcases input_or_collision lhit rhit with eq | collision
        · exact .inl ⟨padded_inj len bound (congrArg Input.block eq), congrArg Input.cv eq⟩
        · exact .inr collision
  | succ more ih =>
    cases lhs with
    | step large lhit ltail =>
      cases rhs with
      | step _ rhit rtail =>
        rcases ih (by simp [len]) ltail rtail with ⟨tails, mids⟩ | collision
        · subst_vars
          rcases input_or_collision lhit rhit with eq | collision
          · have pre := padded_inj (by simp [len]) (by simp) (congrArg Input.block eq)
            exact .inl ⟨by rw [← List.take_append_drop 64 left, ← List.take_append_drop 64 right, pre, tails],
              congrArg Input.cv eq⟩
          · exact .inr collision
        · exact .inr collision

theorem trace_agree {rel : Compression} {root : Bool} {shape : Shape} {lhs rhs : Opening} {output : CV}
    (left : Trace rel root shape lhs output) (right : Trace rel root shape rhs output) :
    Agree lhs rhs ∨ Compression.Collision rel := by
  induction left generalizing rhs with
  | «opaque» => exact .inl (.opaqueLeft ..)
  | leaf ok chain =>
    cases right with
    | «opaque» => exact .inl (.opaqueRight ..)
    | leaf rok rchain =>
      rcases chain_agree (ok.1.trans rok.1.symm) chain rchain with ⟨rfl, _⟩ | collision
      · exact .inl (.leaf _)
      · exact .inr collision
  | fork _ _ hit leftIH rightIH =>
    cases right with
    | «opaque» => exact .inl (.opaqueRight ..)
    | fork left right rhit =>
      rcases input_or_collision hit rhit with eq | collision
      · obtain ⟨leq, req⟩ := parent_inj eq
        subst_vars
        rcases leftIH left with agreeLeft | collision
        · rcases rightIH right with agreeRight | collision
          · exact .inl (.fork agreeLeft agreeRight)
          · exact .inr collision
        · exact .inr collision
      · exact .inr collision

theorem root_agree {rel : Compression} {size : Nat} {digest : Bytes} {lhs rhs : Opening}
    (left : Root rel size digest lhs) (right : Root rel size digest rhs) :
    Agree lhs rhs ∨ Compression.Collision rel := by
  obtain ⟨_, lcv, ltrace, leq⟩ := left
  obtain ⟨_, rcv, rtrace, req⟩ := right
  have eq := digest_inj (leq.trans req.symm)
  subst rcv
  exact trace_agree ltrace rtrace

private theorem chain_canonical {rel : Compression} (canonical : Compression.Canonical rel)
    {root first : Bool} {chunk more : Nat} {cv left right : CV} {bytes : Bytes}
    (lhs : Chain rel root chunk more first cv bytes left) (rhs : Chain rel root chunk more first cv bytes right) :
    left = right := by
  induction lhs generalizing right with
  | last _ hit => cases rhs with | last _ rhit => exact canonical hit rhit
  | step _ hit _ ih =>
    cases rhs with
    | step _ rhit tail =>
      have eq := canonical hit rhit
      subst_vars
      exact ih tail

theorem trace_canonical {rel : Compression} (canonical : Compression.Canonical rel)
    {root : Bool} {shape : Shape} {opening : Opening} {left right : CV}
    (lhs : Trace rel root shape opening left) (rhs : Trace rel root shape opening right) : left = right := by
  induction lhs generalizing right with
  | «opaque» => cases rhs; rfl
  | leaf _ chain => cases rhs with | leaf _ rchain => exact chain_canonical canonical chain rchain
  | fork _ _ hit leftIH rightIH =>
    cases rhs with
    | fork left right rhit =>
      have leq := leftIH left
      have req := rightIH right
      subst_vars
      exact canonical hit rhit

end Silmaril.Proofs.Crypto.Blake3
