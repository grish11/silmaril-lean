module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Calls

@[expose] public section

/-!
# The certificate dispatch keeps the LRAT invariant

The dispatch of one certificate word (`dispatchCode`) only computes locals and calls the LRAT
step functions. Whatever the word and the state, it keeps the view's invariant `InvX X xs` for
the same stream `xs` (the step functions do not extend the stream), and it only writes the
locals `7`, `9`, `10`, `11`. This is stated compositionally: `Seg I code` says that `code`, run
from a state satisfying `I` on an empty operand stack, reaches a state satisfying `I` (in
continuation form, so that the arms of an `if` are proved once, not once per path).

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT
open Silmaril.Wasm.Examples.LratAccept

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

/-- **A code segment keeps `I`**, in continuation form, on an empty operand stack. -/
def Seg (P : Profile) (host : HostSemantics H) (I : Store H → Frame → Prop) (code : List Instr) :
    Prop :=
  ∀ (rest : List Admin) (Q : Post H), (∀ s f, I s f → HWP P host s f (vals ([] : List Val).reverse ++ rest) Q) →
    ∀ s f, I s f → HWP P host s f (vals ([] : List Val).reverse ++ expression code ++ rest) Q

variable {I : Store H → Frame → Prop}

theorem Seg.append {a b : List Instr} (ha : Seg P host I a) (hb : Seg P host I b) :
    Seg P host I (a ++ b) := by
  intro rest Q hr s f hI
  have h := ha (expression b ++ rest) Q (fun s f hI => by
    have := hb rest Q hr s f hI
    simpa [List.append_assoc] using this) s f hI
  simpa [expression, List.map_append, List.append_assoc] using h

/-- The dispatch invariant: the view satisfies `Good xs`, the frame has sixteen `i32` locals
satisfying `J`. -/
def DI (X : Fix H) (xs : List Int) (J : List (BitVec 32) → Prop) : Store H → Frame → Prop :=
  fun s f => InvX X xs s ∧ ∃ L, f = fr X.mi L ∧ L.length = 16 ∧ J L

/-- The locals the dispatch writes. -/
def Writes (k : Nat) : Prop := k = 7 ∨ k = 9 ∨ k = 10 ∨ k = 11

variable {xs : List Int} {J : List (BitVec 32) → Prop}

theorem armEnd_of {rest : List Admin} {Q : Post H}
    (hr : ∀ s f, DI X xs J s f → HWP P host s f (vals ([] : List Val).reverse ++ rest) Q) :
    ∀ s f, DI X xs J s f →
      HWP P host s f (vals ([] : List Val).reverse ++ []) (armPost P host [] rest Q) :=
  fun s f h => w_armEnd (hr s f h)

/-- `if` on a condition computed by `pre` from the locals. -/
theorem seg_if_core {t : List Instr} (ht : Seg P host (DI X xs J) t) {rest : List Admin}
    {Q : Post H} (hr : ∀ s f, DI X xs J s f → HWP P host s f (vals ([] : List Val).reverse ++ rest) Q)
    {s : Store H} {L : List (BitVec 32)} (hI : InvX X xs s) (hL : L.length = 16) (hJ : J L)
    (c : BitVec 32) :
    HWP P host s (fr X.mi L) (vals [Val.i32 c].reverse ++ .plain (ifThen t) :: rest) Q := by
  refine w_if (rs := []) (fun _ => ?_) (fun _ => hr s _ ⟨hI, L, rfl, hL, hJ⟩)
  have := ht [] (armPost P host [] rest Q) (armEnd_of hr) s _ ⟨hI, L, rfl, hL, hJ⟩
  simpa using this

/-- `local.get k; if t`. -/
theorem seg_ifLocal {k : Nat} (hk : k < 16) {t : List Instr} (ht : Seg P host (DI X xs J) t) :
    Seg P host (DI X xs J) [lget k, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) hk ?_
  exact seg_if_core ht hr hI hL hJ _

/-- `local.get k; i32.eqz; if t`. -/
theorem seg_ifEqz {k : Nat} (hk : k < 16) {t : List Instr} (ht : Seg P host (DI X xs J) t) :
    Seg P host (DI X xs J) [lget k, ieqz, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) hk ?_
  refine w_eqz ?_
  exact seg_if_core ht hr hI hL hJ _

/-- `local.get k; i32.const c; i32.eq; if t`. -/
theorem seg_ifEq {k c : Nat} (hk : k < 16) {t : List Instr} (ht : Seg P host (DI X xs J) t) :
    Seg P host (DI X xs J) [lget k, c32 c, ieq, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) hk ?_
  refine w_const ?_
  refine w_rel ?_
  exact seg_if_core ht hr hI hL hJ _

theorem DI.set (hW : ∀ L k v, Writes k → J L → J (L.set k v)) {s : Store H} {L : List (BitVec 32)}
    (hI : InvX X xs s) (hL : L.length = 16) (hJ : J L) {k : Nat} (hk : Writes k) (v : BitVec 32) :
    DI X xs J s (fr X.mi (L.set k v)) :=
  ⟨hI, L.set k v, rfl, by rw [List.length_set, hL], hW L k v hk hJ⟩

theorem writes_lt {k : Nat} (hk : Writes k) : k < 16 := by
  unfold Writes at hk; omega

/-- `i32.const c; local.set k`, for a written local `k`. -/
theorem seg_setc (hW : ∀ L k v, Writes k → J L → J (L.set k v)) {k c : Nat} (hk : Writes k) :
    Seg P host (DI X xs J) [c32 c, lset k] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_const ?_
  refine w_lset (by have := writes_lt hk; omega) (writes_lt hk) ?_
  exact hr s _ (DI.set hW hI hL hJ hk _)

/-- `local.get 5; call j; i32.const c; local.set 9`, for a step function of one argument. -/
theorem seg_call1 (hC : CallsOk P host X) (hW : ∀ L k v, Writes k → J L → J (L.set k v))
    {j c : Nat} (hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 8) :
    Seg P host (DI X xs J) [lget 5, callf j, c32 c, lset 9] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_step1 hC hj hI fun s' hI' => ?_
  refine w_const ?_
  refine w_lset (by omega) (by decide) ?_
  exact hr s' _ (DI.set hW hI' hL hJ (by unfold Writes; omega) _)

/-- `call j; i32.const c; local.set 9`, for a step function without arguments. -/
theorem seg_call0 (hC : CallsOk P host X) (hW : ∀ L k v, Writes k → J L → J (L.set k v))
    {j c : Nat} (hj : j = 5 ∨ j = 9) :
    Seg P host (DI X xs J) [callf j, c32 c, lset 9] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_step0 (rs := []) hC hj hI fun s' hI' => ?_
  refine w_const ?_
  refine w_lset (by omega) (by decide) ?_
  exact hr s' _ (DI.set hW hI' hL hJ (by unfold Writes; omega) _)

theorem seg_classify (hW : ∀ L k v, Writes k → J L → J (L.set k v)) :
    Seg P host (DI X xs J) classifyCode := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [classifyCode, expression, List.map_cons, List.map_nil, List.cons_append, List.append_assoc,
    List.nil_append]
  refine w_lget (by omega) (by decide) ?_
  refine w_const ?_
  refine w_sub ?_
  refine w_const ?_
  refine w_rel ?_
  refine w_lset (by omega) (by decide) ?_
  have h10 := DI.set hW hI hL hJ (k := 10) (by unfold Writes; omega)
  refine w_lget (by simp [hL]) (by decide) ?_
  refine w_const ?_
  refine w_rel ?_
  refine w_lget (by simp [hL]) (by decide) ?_
  refine w_const ?_
  refine w_rel ?_
  refine w_and ?_
  refine w_lset (by simp [hL]) (by decide) ?_
  refine w_const ?_
  refine w_lset (by simp [hL]) (by decide) ?_
  refine hr s _ ⟨hI, _, rfl, by simp [hL], ?_⟩
  exact hW _ 9 _ (by unfold Writes; omega) (hW _ 11 _ (by unfold Writes; omega)
    (hW _ 10 _ (by unfold Writes; omega) hJ))

theorem seg_final (hW : ∀ L k v, Writes k → J L → J (L.set k v)) :
    Seg P host (DI X xs J) [lget 9, lset 7] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_lset (by omega) (by decide) ?_
  exact hr s _ (DI.set hW hI hL hJ (by unfold Writes; omega) _)

theorem seg_ids (hC : CallsOk P host X) (hW : ∀ L k v, Writes k → J L → J (L.set k v))
    {zeroCode : List Instr} (hz : Seg P host (DI X xs J) zeroCode) {j self : Nat}
    (hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 8) :
    Seg P host (DI X xs J) (idsBody zeroCode j self) :=
  Seg.append (a := [lget 5, ieqz, ifThen zeroCode])
    (b := [lget 10, ifThen [lget 5, callf j, c32 self, lset 9]])
    (seg_ifEqz (by decide) hz) (seg_ifLocal (by decide) (seg_call1 hC hW hj))

/-- **The dispatch keeps the invariant.** -/
theorem dispatch_seg (hC : CallsOk P host X) (hW : ∀ L k v, Writes k → J L → J (L.set k v)) :
    Seg P host (DI X xs J) dispatchCode := by
  have hs9 : ∀ c : Nat, Seg P host (DI X xs J) [c32 c, lset 9] := fun _ =>
    seg_setc hW (by unfold Writes; omega)
  unfold dispatchCode
  refine Seg.append (Seg.append (Seg.append (Seg.append (Seg.append (Seg.append (Seg.append
    (Seg.append (Seg.append (Seg.append (seg_classify hW) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    (seg_final hW)
  · refine seg_ifEq (by decide) ?_
    exact Seg.append (Seg.append (seg_ifEq (k := 5) (c := 1) (by decide) (hs9 1))
      (seg_ifEq (k := 5) (c := 2) (by decide) (hs9 4))) (seg_ifEq (k := 5) (c := 3) (by decide) (hs9 5))
  · exact seg_ifEq (by decide) (seg_ifLocal (k := 10) (by decide)
      (seg_call1 (j := 2) (c := 2) hC hW (by omega)))
  · exact seg_ifEq (by decide) (seg_ifLocal (k := 10) (by decide)
      (seg_call1 (j := 2) (c := 6) hC hW (by omega)))
  · exact seg_ifEq (by decide) (Seg.append (seg_ifEqz (k := 5) (by decide) (hs9 3))
      (seg_ifLocal (k := 11) (by decide) (seg_call1 (j := 3) (c := 2) hC hW (by omega))))
  · exact seg_ifEq (by decide) (Seg.append (seg_ifEqz (k := 5) (by decide) (hs9 7))
      (seg_ifLocal (k := 11) (by decide) (seg_call1 (j := 3) (c := 6) hC hW (by omega))))
  · exact seg_ifEq (by decide) (seg_ids (j := 4) (self := 3) hC hW
      (seg_call0 (j := 5) (c := 0) hC hW (by omega)) (by omega))
  · exact seg_ifEq (by decide) (seg_ids (j := 6) (self := 4) hC hW (hs9 0) (by omega))
  · exact seg_ifEq (by decide) (seg_ids (j := 8) (self := 8) hC hW
      (seg_call0 (j := 9) (c := 0) hC hW (by omega)) (by omega))
  · exact seg_ifEq (by decide) (seg_ids (j := 4) (self := 8) hC hW (hs9 7) (by omega))

end Silmaril.Proofs.Wasm.Examples.LratAccept
