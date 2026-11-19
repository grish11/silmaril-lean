module

public import Silmaril.Wasm.Examples.LRAT.Thms
public import Silmaril.Wasm.Examples.LratAccept.Defs
public import Silmaril.Wasm.Acceptor.Code.Thms

@[expose] public section

/-!
# The LRAT functions inside a bigger module: call specifications and call rules

`lratModule`'s bodies are proved over the view `Shape X s G B` of a fixture `X`
(`Silmaril.Wasm.Examples.LRAT.Fix`), which allows further globals and memories after the
checker's. Here the ten LRAT functions get **function specifications** in any fixture whose
functions `0 … 9` are the module's (`CodeOk`): from a store whose view satisfies `Good xs` for
some stream `xs` (`InvX X xs s`), `add_lit(x)` reaches `InvX X (xs ++ [x.toInt])`,
`end_clause()` reaches `InvX X (xs ++ [0])`, the other void functions keep `InvX X xs`, and
`unsat()` answers `v` with `v ≠ 0 → (Dimacs.cnf xs).Unsat` (`callsOk`). The **call rules**
`w_call…` use them for `call j` in the symbolic execution of a caller in the same module (from
the acceptor kit's `Silmaril.Wasm.Acceptor.w_call`).

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Examples.LratAccept (callf)
open Silmaril.Logic.SAT
open Silmaril.Wasm.Acceptor (w_call)

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

/-! ## The fixture -/

/-- The functions `0 … 9` of the fixture are `lratModule`'s, in the module instance `X.mi`,
which resolves them to the addresses `0 … 9`. -/
structure CodeOk (X : Fix H) : Prop where
  fn : ∀ j < 10, ∃ (fi : FuncInst H) (f : Func) (ty : CCompType),
    X.fs[j]? = some fi ∧ lratModule.funcs[j]? = some f ∧ lratTys[j]? = some ty ∧
    fi.code = .wasm f ∧ fi.module = X.mi ∧ Expand fi.type ty
  addr : ∀ j < 10, X.mi.funcs[j]? = some j

/-! ## Specifications -/

/-- `n` `i32` arguments. -/
def ArgsI32 (n : Nat) (args : List Val) : Prop := ∃ L : List (BitVec 32), L.length = n ∧ args = L.map Val.i32

/-- **A void LRAT function** of `n` arguments extending the stream by `c args`. -/
def vspec (X : Fix H) (n : Nat) (c : List Val → List Int) : FSpec H where
  pre s args := ArgsI32 n args ∧ ∃ xs, InvX X xs s
  post s args s' o := o = .normal [] ∧ ∀ xs, InvX X xs s → InvX X (xs ++ c args) s'

/-- **`unsat()`**: the answer is nonzero only for an unsatisfiable stream. -/
def uspec (X : Fix H) : FSpec H where
  pre s args := args = [] ∧ ∃ xs, InvX X xs s
  post s _ s' o := ∃ v : BitVec 32, o = .normal [Val.i32 v] ∧
    ∀ xs, InvX X xs s → InvX X xs s' ∧ (v ≠ 0#32 → (Dimacs.cnf xs).Unsat)

/-- The specifications of the ten LRAT functions hold. -/
structure CallsOk (P : Profile) (host : HostSemantics H) (X : Fix H) : Prop where
  code : CodeOk X
  addLit : FSpecValid P host 0 (vspec X 1 fun args => [argInt args])
  endClause : FSpecValid P host 1 (vspec X 0 fun _ => [0])
  step1 : ∀ j, j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 8 → FSpecValid P host j (vspec X 1 fun _ => [])
  step0 : ∀ j, j = 5 ∨ j = 9 → FSpecValid P host j (vspec X 0 fun _ => [])
  unsat : FSpecValid P host 7 (uspec X)

theorem shape_of_inv {xs : List Int} {s : Store H} (h : InvX X xs s) : s.funcs = X.fs := by
  obtain ⟨G, B, hS, -⟩ := h
  exact hS.funcs

/-- A void function's specification from its body. -/
theorem vspec_valid {j n : Nat} {c : List Val → List Int} {fi : FuncInst H} {fn : Func}
    {ps rs : Ty (.list .val)} (hfi : X.fs[j]? = some fi) (hcode : fi.code = .wasm fn)
    (hexp : Expand fi.type (.func ps rs)) (hps : ps.length = n) (hrs : rs.length = 0)
    (hmod : fi.module = X.mi)
    (hbody : ∀ (s : Store H) G B xs (L : List (BitVec 32)), L.length = n → Shape X s G B →
      Good xs G B → HWP P host s (Frame.forCall X.mi (L.map Val.i32) fn.locals)
        (expression fn.body) (stepPost X G B (c (L.map Val.i32)))) :
    FSpecValid P host j (vspec X n c) := by
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => ?_) fun s args hpre => ?_
  · obtain ⟨-, xs, hI⟩ := hpre
    rw [shape_of_inv hI]; exact hfi
  · obtain ⟨⟨L, hL, rfl⟩, -⟩ := hpre
    simp [hL, hps]
  · obtain ⟨⟨L, hL, rfl⟩, xs, G, B, hS, hG⟩ := hpre
    rw [hmod, hrs]
    refine HWP.mono (fun s' F o h => ?_) (hbody s G B xs L hL hS hG)
    obtain ⟨rfl, G', B', hS', hG'⟩ := h
    refine ⟨rfl, rfl, fun ys hI => ?_⟩
    obtain ⟨G₁, B₁, hS₁, hG₁⟩ := hI
    obtain ⟨rfl, rfl⟩ := hS.unique hS₁
    exact ⟨G', B', hS', hG' ys hG₁⟩

/-- The function `j < 10` of the fixture. -/
theorem code_fn (hc : CodeOk X) {j : Nat} (hj : j < 10) {f : Func} {ty : CCompType}
    (hf : lratModule.funcs[j]? = some f) (hty : lratTys[j]? = some ty) :
    ∃ fi : FuncInst H, X.fs[j]? = some fi ∧ fi.code = .wasm f ∧ fi.module = X.mi ∧
      Expand fi.type ty := by
  obtain ⟨fi, f', ty', h1, h2, h3, h4, h5, h6⟩ := hc.fn j hj
  rw [hf] at h2; rw [hty] at h3
  cases h2; cases h3
  exact ⟨fi, h1, h4, h5, h6⟩

/-- `L.length = 1`. -/
theorem len_one {L : List (BitVec 32)} (h : L.length = 1) : ∃ x, L = [x] := by
  match L, h with
  | [x], _ => exact ⟨x, rfl⟩

theorem len_zero {L : List (BitVec 32)} (h : L.length = 0) : L = [] := List.eq_nil_of_length_eq_zero h

set_option maxHeartbeats 1000000 in
/-- **The LRAT functions meet their specifications** in every fixture holding their code. -/
theorem callsOk (hX : MiOk X) (hc : CodeOk X) : CallsOk P host X := by
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 0) (by decide) rfl rfl
    refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
    obtain ⟨x, rfl⟩ := len_one hL
    obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
    rw [← code_eq]
    exact addLit_hwp hX hS hG (x := x)
  · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 1) (by decide) rfl rfl
    refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
    obtain rfl := len_zero hL
    obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
    rw [← code_eq]
    have hb := addLit_hwp (P := P) (host := host) hX hS hG (x := 0)
    unfold AddLitHwp at hb
    rw [show ((0 : BitVec 32).toInt) = 0 from rfl] at hb
    exact hb
  · rintro j (rfl | rfl | rfl | rfl | rfl)
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 2) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain ⟨x, rfl⟩ := len_one hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact stepBegin_hwp hX hS hG x
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 3) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain ⟨x, rfl⟩ := len_one hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact stepLit_hwp hX hS hG x
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 4) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain ⟨x, rfl⟩ := len_one hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact stepHint_hwp hX hS hG x
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 6) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain ⟨x, rfl⟩ := len_one hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact delete_hwp hX hS x
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 8) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain ⟨x, rfl⟩ := len_one hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact ratBegin_hwp hX hS hG x
  · rintro j (rfl | rfl)
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 5) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain rfl := len_zero hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact stepEnd_hwp hX hS hG
    · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 9) (by decide) rfl rfl
      refine vspec_valid hfi hcode hexp rfl rfl hmod fun s G B xs L hL hS hG => ?_
      obtain rfl := len_zero hL
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [← code_eq]
      exact ratEnd_hwp hX hS hG
  · obtain ⟨fi, hfi, hcode, hmod, hexp⟩ := code_fn hc (j := 7) (by decide) rfl rfl
    refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
      (fun _ _ hpre => by rw [hpre.1]; rfl) fun s args hpre => ?_
    · obtain ⟨-, xs, hI⟩ := hpre
      rw [shape_of_inv hI]; exact hfi
    · obtain ⟨rfl, xs, G, B, hS, hG⟩ := hpre
      obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
      rw [hmod, ← code_eq]
      refine HWP.mono (fun s' F o h => ?_) (unsat_hwp hX hS)
      obtain ⟨v, rfl, hS', hu⟩ := h
      refine ⟨rfl, v, rfl, fun ys hI => ?_⟩
      obtain ⟨G₁, B₁, hS₁, hG₁⟩ := hI
      obtain ⟨rfl, rfl⟩ := hS.unique hS₁
      exact ⟨⟨_, _, hS', hG₁⟩, hu ys hG₁⟩

/-! ## Call rules -/

variable {s : Store H} {L : List (BitVec 32)} {rs : List Val} {rest : List Admin} {Q : Post H}
  {xs : List Int}

theorem fs_of_inv (hc : CodeOk X) (hI : InvX X xs s) {j : Nat} (hj : j < 10) :
    ∃ fi, s.funcs[j]? = some fi := by
  obtain ⟨fi, -, -, h, -⟩ := hc.fn j hj
  exact ⟨fi, by rw [shape_of_inv hI]; exact h⟩

/-- A void call, after which the continuation must hold from every store with `InvX X ys`. -/
theorem w_callv {j n : Nat} {c : List Val → List Int} {args : List Val} (hc : CodeOk X)
    (hj : j < 10) (hS : FSpecValid P host j (vspec X n c)) (ha : ArgsI32 n args)
    (hI : InvX X xs s)
    (k : ∀ s', InvX X (xs ++ c args) s' → HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (rs.reverse ++ args) ++ .plain (callf j) :: rest) Q := by
  obtain ⟨fi, hf⟩ := fs_of_inv hc hI hj
  refine w_call (by omega) (hc.addr j hj) hf hS ⟨ha, xs, hI⟩ fun s' o h => ?_
  obtain ⟨-, ⟨res, rfl, hp, hq⟩ | ⟨rfl, hp, -⟩ | ⟨a, rfl, hp, -⟩⟩ := h
  · cases hp
    simpa [seqPost] using k s' (hq xs hI)
  · cases hp
  · cases hp

/-- `add_lit(x)`. -/
theorem w_addLit (hC : CallsOk P host X) (hI : InvX X xs s) {x : BitVec 32}
    (k : ∀ s', InvX X (xs ++ [x.toInt]) s' →
      HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 x :: rs).reverse ++ .plain (callf 0) :: rest) Q := by
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 x).toAdmin] =
    vals (rs.reverse ++ [Val.i32 x]) by simp]
  exact w_callv hC.code (by decide) hC.addLit ⟨[x], rfl, rfl⟩ hI k

/-- `end_clause()`. -/
theorem w_endClause (hC : CallsOk P host X) (hI : InvX X xs s)
    (k : ∀ s', InvX X (xs ++ [0]) s' → HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals rs.reverse ++ .plain (callf 1) :: rest) Q := by
  have := w_callv (args := []) hC.code (by decide) hC.endClause ⟨[], rfl, rfl⟩ hI k
  simpa using this

/-- A step function of one argument (`step_begin`, `step_lit`, `step_hint`, `delete`,
`rat_begin`). -/
theorem w_step1 (hC : CallsOk P host X) {j : Nat} (hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 8)
    (hI : InvX X xs s) {x : BitVec 32}
    (k : ∀ s', InvX X xs s' → HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 x :: rs).reverse ++ .plain (callf j) :: rest) Q := by
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 x).toAdmin] =
    vals (rs.reverse ++ [Val.i32 x]) by simp]
  exact w_callv hC.code (by omega) (hC.step1 j hj) ⟨[x], rfl, rfl⟩ hI
    fun s' h => k s' (by simpa using h)

/-- A step function without arguments (`step_end`, `rat_end`). -/
theorem w_step0 (hC : CallsOk P host X) {j : Nat} (hj : j = 5 ∨ j = 9) (hI : InvX X xs s)
    (k : ∀ s', InvX X xs s' → HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals rs.reverse ++ .plain (callf j) :: rest) Q := by
  have := w_callv (args := []) hC.code (by omega) (hC.step0 j hj) ⟨[], rfl, rfl⟩ hI
    fun s' h => k s' (by simpa using h)
  simpa using this

/-- `unsat()`. -/
theorem w_unsat (hC : CallsOk P host X) (hI : InvX X xs s)
    (k : ∀ s' v, InvX X xs s' → (v ≠ 0#32 → (Dimacs.cnf xs).Unsat) →
      HWP P host s' (fr X.mi L) (vals (Val.i32 v :: rs).reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals rs.reverse ++ .plain (callf 7) :: rest) Q := by
  obtain ⟨fi, hf⟩ := fs_of_inv hC.code hI (j := 7) (by decide)
  have := w_call (f := fr X.mi L) (j := 7) (a := 7) (vs₀ := rs.reverse) (args := []) (rest := rest) (Q := Q)
    (by decide)
    (hC.code.addr 7 (by decide)) hf hC.unsat ⟨rfl, xs, hI⟩ fun s' o h => ?_
  · simpa using this
  · obtain ⟨-, ⟨res, rfl, v, hv, hq⟩ | ⟨rfl, v, hv, -⟩ | ⟨a, rfl, v, hv, -⟩⟩ := h
    · cases hv
      obtain ⟨hI', hu⟩ := hq xs hI
      simpa [seqPost] using k s' v hI' hu
    · cases hv
    · cases hv

end Silmaril.Proofs.Wasm.Examples.LratAccept
