module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Abi
public import Silmaril.Proofs.Wasm.Examples.LratAccept.Parse

@[expose] public section

/-!
# The certificate dispatch computes the parser automaton

`dispatch_val`: one run of `dispatchCode` on the word `x` (local `5`) in the parse state `st`
(local `7`) ends with local `7` holding `dispV st x`, and `dispV (n : BitVec 32) x` is
`certStep n x` for every state `n ≤ 9` (`dispV_eq`). Together with `dispatch_seg` (the LRAT
invariant is kept, `Dispatch`) this makes the certificate loop a run of `certRun`.

The proof follows the code: the classification (`classifyCode`) computes "positive" and
"literal word" (locals `10`, `11`) and the default next state `9` (local `9`); each guard
`guardOn k body` changes local `9` only when `st = k` (`Tri`: a segment from a precondition to
a postcondition, in continuation form, as `Seg`); the last two instructions copy local `9` to
local `7`.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Logic.SAT.Carrier (LitWord)

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

/-- **A code segment from `I` to `O`**, in continuation form, on an empty operand stack. -/
def Tri (P : Profile) (host : HostSemantics H) (I O : Store H → Frame → Prop)
    (code : List Instr) : Prop :=
  ∀ (rest : List Admin) (Q : Post H),
    (∀ s f, O s f → HWP P host s f (vals ([] : List Val).reverse ++ rest) Q) →
    ∀ s f, I s f → HWP P host s f (vals ([] : List Val).reverse ++ expression code ++ rest) Q

theorem Tri.append {I M O : Store H → Frame → Prop} {a b : List Instr}
    (ha : Tri P host I M a) (hb : Tri P host M O b) : Tri P host I O (a ++ b) := by
  intro rest Q hr s f hI
  have h := ha (expression b ++ rest) Q (fun s f hI => by
    have := hb rest Q hr s f hI
    simpa [List.append_assoc] using this) s f hI
  simpa [expression, List.map_append, List.append_assoc] using h

/-! ## The values the dispatch tracks -/

/-- The classified word: the frame condition `J`, the word `x` in local `5`, the state `st` in
local `7`, "positive" and "literal word" in locals `10`, `11`, the next state `v` in local `9`. -/
def Cls (J : List (BitVec 32) → Prop) (x st v : BitVec 32) (L : List (BitVec 32)) : Prop :=
  J L ∧ L.getD 5 0 = x ∧ L.getD 7 0 = st ∧ L.getD 10 0 = b32 (0 < x.toInt) ∧
    L.getD 11 0 = b32 (LitWord x = true) ∧ L.getD 9 0 = v

variable {xs : List Int} {J : List (BitVec 32) → Prop} {x st : BitVec 32}

theorem Cls.set9 (hW : ∀ L k v, Writes k → J L → J (L.set k v)) {L : List (BitVec 32)}
    (hL : L.length = 16) {v : BitVec 32} (h : Cls J x st v L) (w : BitVec 32) :
    Cls J x st w (L.set 9 w) := by
  obtain ⟨hJ, h5, h7, h10, h11, -⟩ := h
  exact ⟨hW L 9 w (by unfold Writes; omega) hJ, by rw [getD_set_ne (by omega)]; exact h5,
    by rw [getD_set_ne (by omega)]; exact h7, by rw [getD_set_ne (by omega)]; exact h10,
    by rw [getD_set_ne (by omega)]; exact h11, getD_set_self (by omega) w⟩

theorem ite_pos' {c : Prop} [Decidable c] (h : c) {α : Type} (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] (h : ¬ c) {α : Type} (a b : α) :
    (if c then a else b) = b := by simp [h]

section
variable (hW : ∀ L k v, Writes k → J L → J (L.set k v))
include hW

/-- `i32.const c; local.set 9`. -/
theorem tri_set9 (v : BitVec 32) (c : Nat) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (BitVec.ofNat 32 c))) [c32 c, lset 9] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hC⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_const ?_
  refine w_lset (by omega) (by decide) ?_
  exact hr s _ ⟨hI, _, rfl, by simp [hL], hC.set9 hW hL _⟩

/-- `local.get 5; call j; i32.const c; local.set 9`. -/
theorem tri_call1 (hC : CallsOk P host X) {j : Nat} (hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 8)
    (v : BitVec 32) (c : Nat) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (BitVec.ofNat 32 c)))
      [lget 5, callf j, c32 c, lset 9] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_step1 hC hj hI fun s' hI' => ?_
  refine w_const ?_
  refine w_lset (by omega) (by decide) ?_
  exact hr s' _ ⟨hI', _, rfl, by simp [hL], hK.set9 hW hL _⟩

/-- `call j; i32.const c; local.set 9`. -/
theorem tri_call0 (hC : CallsOk P host X) {j : Nat} (hj : j = 5 ∨ j = 9) (v : BitVec 32)
    (c : Nat) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (BitVec.ofNat 32 c)))
      [callf j, c32 c, lset 9] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_step0 (rs := []) hC hj hI fun s' hI' => ?_
  refine w_const ?_
  refine w_lset (by omega) (by decide) ?_
  exact hr s' _ ⟨hI', _, rfl, by simp [hL], hK.set9 hW hL _⟩

end

/-- `if` on the truth value of `c`: the arm moves local `9` from `v` to `w`. -/
theorem tri_if_core {c : Prop} [Decidable c] {t : List Instr} {v w : BitVec 32}
    (ht : c → Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st w)) t)
    {rest : List Admin} {Q : Post H}
    (hr : ∀ s f, DI X xs (Cls J x st (if c then w else v)) s f →
      HWP P host s f (vals ([] : List Val).reverse ++ rest) Q)
    {s : Store H} {L : List (BitVec 32)} (hI : InvX X xs s) (hL : L.length = 16)
    (hK : Cls J x st v L) :
    HWP P host s (fr X.mi L) (vals [Val.i32 (b32 c)].reverse ++ .plain (ifThen t) :: rest) Q := by
  refine w_if (rs := []) (fun hc => ?_) (fun hc => ?_)
  · have hc' := b32_ne_zero.1 hc
    have := ht hc' [] (armPost P host [] rest Q)
      (fun s f h => w_armEnd (hr s f (by rw [ite_pos' hc']; exact h))) s _ ⟨hI, L, rfl, hL, hK⟩
    simpa using this
  · have hc' := b32_eq_zero.1 hc
    exact hr s _ (by rw [ite_neg' hc']; exact ⟨hI, L, rfl, hL, hK⟩)

/-- `local.get 7; i32.const k; i32.eq; if t`: a guard on the state. -/
theorem tri_guard {k : Nat} {t : List Instr} {v w : BitVec 32}
    (ht : st = BitVec.ofNat 32 k → Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st w)) t) :
    Tri P host (DI X xs (Cls J x st v))
      (DI X xs (Cls J x st (if st = BitVec.ofNat 32 k then w else v))) (guardOn k t) := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [guardOn, expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_const ?_
  refine w_eq ?_
  rw [hK.2.2.1]
  exact tri_if_core ht hr hI hL hK

/-- `local.get 5; i32.const k; i32.eq; if t`: a test of the word. -/
theorem tri_ifWord {k : Nat} {t : List Instr} {v w : BitVec 32}
    (ht : x = BitVec.ofNat 32 k → Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st w)) t) :
    Tri P host (DI X xs (Cls J x st v))
      (DI X xs (Cls J x st (if x = BitVec.ofNat 32 k then w else v))) [lget 5, c32 k, ieq, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_const ?_
  refine w_eq ?_
  rw [hK.2.1]
  exact tri_if_core ht hr hI hL hK

/-- `local.get 5; i32.eqz; if t`. -/
theorem tri_ifZero {t : List Instr} {v w : BitVec 32}
    (ht : x = 0 → Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st w)) t) :
    Tri P host (DI X xs (Cls J x st v))
      (DI X xs (Cls J x st (if x = 0 then w else v))) [lget 5, ieqz, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_eqz' ?_
  rw [hK.2.1]
  exact tri_if_core ht hr hI hL hK

/-- `local.get 10; if t`: the word is positive. -/
theorem tri_ifPos {t : List Instr} {v w : BitVec 32}
    (ht : 0 < x.toInt → Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st w)) t) :
    Tri P host (DI X xs (Cls J x st v))
      (DI X xs (Cls J x st (if 0 < x.toInt then w else v))) [lget 10, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  rw [hK.2.2.2.1]
  exact tri_if_core ht hr hI hL hK

/-- `local.get 11; if t`: the word is a literal word. -/
theorem tri_ifLit {t : List Instr} {v w : BitVec 32}
    (ht : LitWord x = true → Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st w)) t) :
    Tri P host (DI X xs (Cls J x st v))
      (DI X xs (Cls J x st (if LitWord x = true then w else v))) [lget 11, ifThen t] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  rw [hK.2.2.2.2.1]
  exact tri_if_core ht hr hI hL hK

/-! ## The classification and the final copy -/

theorem b32_congr' {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : b32 p = b32 q := by
  unfold b32; by_cases hp : p <;> simp_all

theorem intMin_eq' : BitVec.intMin 32 = BitVec.ofNat 32 2147483648 := by decide

theorem pos_iff (x : BitVec 32) :
    (x - BitVec.ofNat 32 1).toNat < (BitVec.ofNat 32 2147483647).toNat ↔ 0 < x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> bv_omega

theorem lit_iff (x : BitVec 32) :
    (x ≠ BitVec.ofNat 32 0 ∧ x ≠ BitVec.ofNat 32 2147483648) ↔ LitWord x = true := by
  simp [LitWord, intMin_eq']

/-- The classification of the word in local `5`. -/
theorem tri_classify (hW : ∀ L k v, Writes k → J L → J (L.set k v)) :
    Tri P host (DI X xs (fun L => J L ∧ L.getD 5 0 = x ∧ L.getD 7 0 = st))
      (DI X xs (Cls J x st (BitVec.ofNat 32 9))) classifyCode := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hJ, h5, h7⟩
  simp only [classifyCode, expression, List.map_cons, List.map_nil, List.cons_append,
    List.append_assoc, List.nil_append]
  refine w_lget (by omega) (by decide) ?_
  refine w_const ?_
  refine w_sub ?_
  refine w_const ?_
  refine w_ltu ?_
  refine w_lset (by omega) (by decide) ?_
  refine w_lget (by simp [hL]) (by decide) ?_
  refine w_const ?_
  refine w_ne ?_
  refine w_lget (by simp [hL]) (by decide) ?_
  refine w_const ?_
  refine w_ne ?_
  refine w_and ?_
  refine w_lset (by simp [hL]) (by decide) ?_
  refine w_const ?_
  refine w_lset (by simp [hL]) (by decide) ?_
  refine hr s _ ⟨hI, _, rfl, by simp [hL], ?_⟩
  refine ⟨hW _ 9 _ (by unfold Writes; omega) (hW _ 11 _ (by unfold Writes; omega)
    (hW _ 10 _ (by unfold Writes; omega) hJ)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega)]; exact h5
  · rw [getD_set_ne (by omega), getD_set_ne (by omega), getD_set_ne (by omega)]; exact h7
  · rw [getD_set_ne (by omega), getD_set_ne (by omega), getD_set_self (by omega), h5]
    exact b32_congr' (pos_iff x)
  · rw [getD_set_ne (by omega), getD_set_self (by simp [hL]), getD_set_ne (by omega), h5, b32_and]
    exact b32_congr' (lit_iff x)
  · exact getD_set_self (by simp [hL]) _

/-- `local.get 9; local.set 7`: the next state becomes the state. -/
theorem tri_final (hW : ∀ L k v, Writes k → J L → J (L.set k v)) (v : BitVec 32) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (fun L => J L ∧ L.getD 7 0 = v)) [lget 9, lset 7] := by
  rintro rest Q hr s f ⟨hI, L, rfl, hL, hK⟩
  simp only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine w_lget (by omega) (by decide) ?_
  refine w_lset (by omega) (by decide) ?_
  refine hr s _ ⟨hI, _, rfl, by simp [hL], hW L 7 _ (by unfold Writes; omega) hK.1, ?_⟩
  rw [getD_set_self (by omega)]
  exact hK.2.2.2.2.2

/-! ## The dispatch -/

/-- The next state of the guards, from the next state `v` so far: a tag. -/
def tagV (x v : BitVec 32) : BitVec 32 :=
  if x = BitVec.ofNat 32 3 then BitVec.ofNat 32 5 else
  if x = BitVec.ofNat 32 2 then BitVec.ofNat 32 4 else
  if x = BitVec.ofNat 32 1 then BitVec.ofNat 32 1 else v

/-- An id (`idBody next`). -/
def idV (x : BitVec 32) (next : Nat) (v : BitVec 32) : BitVec 32 :=
  if 0 < x.toInt then BitVec.ofNat 32 next else v

/-- Literals (`litsBody z self`). -/
def litsV (x : BitVec 32) (z self : Nat) (v : BitVec 32) : BitVec 32 :=
  if LitWord x = true then BitVec.ofNat 32 self else if x = 0 then BitVec.ofNat 32 z else v

/-- Ids (`idsBody … self`, with the next state `z` on `0`). -/
def idsV (x : BitVec 32) (z self : Nat) (v : BitVec 32) : BitVec 32 :=
  if 0 < x.toInt then BitVec.ofNat 32 self else if x = 0 then BitVec.ofNat 32 z else v

/-- A guard. -/
def gV (st : BitVec 32) (k : Nat) (w v : BitVec 32) : BitVec 32 :=
  if st = BitVec.ofNat 32 k then w else v

/-- **The state after the dispatch.** -/
def dispV (st x : BitVec 32) : BitVec 32 :=
  let v0 := BitVec.ofNat 32 9
  let v1 := gV st 0 (tagV x v0) v0
  let v2 := gV st 1 (idV x 2 v1) v1
  let v3 := gV st 5 (idV x 6 v2) v2
  let v4 := gV st 2 (litsV x 3 2 v3) v3
  let v5 := gV st 6 (litsV x 7 6 v4) v4
  let v6 := gV st 3 (idsV x 0 3 v5) v5
  let v7 := gV st 4 (idsV x 0 4 v6) v6
  let v8 := gV st 7 (idsV x 0 8 v7) v7
  gV st 8 (idsV x 7 8 v8) v8

section
variable (hC : CallsOk P host X) (hW : ∀ L k v, Writes k → J L → J (L.set k v))
include hC hW

omit hC in
theorem tri_tag (v : BitVec 32) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (tagV x v))) tagBody :=
  Tri.append (Tri.append (tri_ifWord (k := 1) fun _ => tri_set9 hW v 1)
    (tri_ifWord (k := 2) fun _ => tri_set9 hW _ 4)) (tri_ifWord (k := 3) fun _ => tri_set9 hW _ 5)

theorem tri_id (next : Nat) (v : BitVec 32) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (idV x next v))) (idBody next) :=
  tri_ifPos fun _ => tri_call1 hW hC (j := 2) (by omega) v next

theorem tri_lits (z self : Nat) (v : BitVec 32) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (litsV x z self v)))
      (litsBody z self) :=
  Tri.append (tri_ifZero fun _ => tri_set9 hW v z)
    (tri_ifLit fun _ => tri_call1 hW hC (j := 3) (by omega) _ self)

theorem tri_ids {zeroCode : List Instr} {z : Nat}
    (hz : ∀ v, Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (BitVec.ofNat 32 z)))
      zeroCode)
    {j : Nat} (hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 8) (self : Nat) (v : BitVec 32) :
    Tri P host (DI X xs (Cls J x st v)) (DI X xs (Cls J x st (idsV x z self v)))
      (idsBody zeroCode j self) :=
  Tri.append (tri_ifZero fun _ => hz v) (tri_ifPos fun _ => tri_call1 hW hC hj _ self)

/-- **The dispatch computes `dispV`.** -/
theorem dispatch_val :
    Tri P host (DI X xs (fun L => J L ∧ L.getD 5 0 = x ∧ L.getD 7 0 = st))
      (DI X xs (fun L => J L ∧ L.getD 7 0 = dispV st x)) dispatchCode := by
  unfold dispatchCode
  refine Tri.append (Tri.append (Tri.append (Tri.append (Tri.append (Tri.append (Tri.append
    (Tri.append (Tri.append (Tri.append (tri_classify hW)
      (tri_guard (k := 0) fun _ => tri_tag hW _))
      (tri_guard (k := 1) fun _ => tri_id hC hW 2 _))
      (tri_guard (k := 5) fun _ => tri_id hC hW 6 _))
      (tri_guard (k := 2) fun _ => tri_lits hC hW 3 2 _))
      (tri_guard (k := 6) fun _ => tri_lits hC hW 7 6 _))
      (tri_guard (k := 3) fun _ => tri_ids hC hW (fun v => tri_call0 hW hC (j := 5) (by omega) v 0)
        (j := 4) (by omega) 3 _))
      (tri_guard (k := 4) fun _ => tri_ids hC hW (fun v => tri_set9 hW v 0) (j := 6) (by omega) 4 _))
      (tri_guard (k := 7) fun _ => tri_ids hC hW (fun v => tri_call0 hW hC (j := 9) (by omega) v 0)
        (j := 8) (by omega) 8 _))
      (tri_guard (k := 8) fun _ => tri_ids hC hW (fun v => tri_set9 hW v 7) (j := 4) (by omega) 8 _))
    (tri_final hW _)

end

set_option linter.unusedTactic false in
/-- **`dispV` is the parser automaton** on its states. -/
theorem dispV_eq {n : Nat} (hn : n ≤ 9) (x : BitVec 32) :
    dispV (BitVec.ofNat 32 n) x = BitVec.ofNat 32 (certStep n x) := by
  have hl0 : LitWord 0#32 = false := by decide
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first
    | omega
    | (by_cases hx : x = 0 <;>
        simp [dispV, gV, tagV, idV, litsV, idsV, certStep, hx, hl0] <;>
        (try split_ifs) <;> simp_all)

end Silmaril.Proofs.Wasm.Examples.LratAccept
