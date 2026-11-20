module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Basic

/-!
# Reader checkers: rules for any list of imports

The rules of `Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Basic` fix the five cons reader
imports, each of one `i32` parameter. Here the imports are any list `fts` of function types:

* `hwp_importN`: the import call rule for any arguments;
* `get_importsG`, `importOp?_existsG`, `results_ofG`: questions and typed answers of an
  instance whose imports are `fts`;
* more straight-line rules (`X.rel32`, `X.add32`, `X.blockEnd'`);
* `ieqG`: executable equality on a larger instruction fragment (adds `intBinOp`, `block`,
  `brIf`, `drop`);
* `GShape`: the shape of an instantiated module with imports `fts`, one export of type `eft`
  implemented by the function after the import stubs (checked by kernel evaluation of
  `gshapeOk`), and `X.callG`, the import call rule for it;
* `gameSat_ofG`: the body-to-`GameSat` step for the trivial export specification.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

/-! ## Straight-line rules -/

theorem X.rel32 {op : IntRelOp} {x y : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 (Numerics.intRelOp .i32 op x y)]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 x] ++ [.i32 y]) ++ expression (.intRelOp .i32 op :: is)) Q := by
  rw [List.append_assoc]
  exact Wp.intRelOp (m := .part) (t := .i32) (x := x) (y := y) h

theorem X.add32 {x y : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 (x + y)]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 x] ++ [.i32 y]) ++ expression (.intBinOp .i32 .add :: is)) Q := by
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := y) (z := x + y) rfl h

/-- The end of the function body, falling through with no values. -/
theorem X.done (hq : Q s f (.normal [])) : HWP P host s f (vals [] ++ expression []) Q :=
  HWP.of_vals hq

/-! ## Import calls with any arguments -/

section ImportN

variable {I : ScalarInstance} {Ii : ISpec I.E}

/-- A call of import `k` (the host stub at address `k`) with the arguments `args`: from an
allowed question, every allowed answer must make the rest safe. -/
theorem hwp_importN {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val}
    (hx : f.module.funcs[x.toNat]? = some k) (hf : s.funcs[k]? = some fk) (hcode : fk.code = .host k)
    (he : Expand fk.type (.func ps rs)) (hps : ps.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ Ii.pre e)
    (hk : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Leaves Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    have hS : importCtx I Ii (id k) = some (importSpec I Ii k) := rfl
    refine Safe.callIdx (x := x) (S := Silmaril.Wasm.Logic.Open.stubSpec k k (importSpec I Ii k)) hx hf
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS n) ⟨⟨fk, ps, rs, hf, hcode, he, hps.symm⟩, hop⟩ ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · obtain ⟨rfl, hall⟩ := hR
      obtain ⟨e, he', -⟩ := hop
      obtain ⟨v, hv, ho⟩ := hall e he'
      have hr : Answer.toResult (ft := I.imports.get e.1) v = .values res := by
        revert ho
        cases v <;> simp [Answer.toResult, resultOutcome]
      exact hk e v he' hv res hr n
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).2.1
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).2.2 y

end ImportN

/-! ## Questions and answers of an instance with imports `fts` -/

section Gen

variable {I : ScalarInstance} {fts : List FnType} (hI : I.imports = fts)

include hI

theorem get_importsG (i : Fin I.imports.length) :
    I.imports.get i = fts[i.val]'(by simpa [hI] using i.2) := by
  rw [List.get_eq_getElem]
  exact List.getElem_of_eq hI i.2

theorem importOp?_existsG {k : Nat} (hk : k < fts.length) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (fts[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e := by
  have hlt : k < I.imports.length := by simpa [hI] using hk
  have ht' : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨k, hlt⟩).params args := by
    rw [get_importsG hI]
    exact ht
  exact ⟨⟨⟨k, hlt⟩, ⟨args, ht'⟩⟩,
    by simp only [ScalarInstance.importOp?, ifaceOp?, dite_eq_left hlt, dite_eq_left ht']⟩

/-- The typed results of an answer. -/
theorem results_ofG {e : I.E.Op} {v : I.E.Ar e} {res : List Val}
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    List.Forall₂ ScalarType.HasVal (fts[e.1.val]'(by simpa [hI] using e.1.2)).results res ∧
      ansVals v = some res := by
  rcases v with ⟨vs, hvs⟩ | _ | _
  · simp only [Answer.toResult, Result.values.injEq] at hr
    subst hr
    exact ⟨get_importsG hI e.1 ▸ hvs, rfl⟩
  · cases hr
  · cases hr

end Gen

theorem res_i32 {res : List Val} (h : List.Forall₂ ScalarType.HasVal [.num (.int .i32)] res) :
    ∃ c, res = [.i32 c] := by
  rcases h with _ | ⟨⟨c, rfl⟩, hnil⟩
  cases hnil
  exact ⟨c, rfl⟩

theorem res_i64 {res : List Val} (h : List.Forall₂ ScalarType.HasVal [.num (.int .i64)] res) :
    ∃ w, res = [.i64 w] := by
  rcases h with _ | ⟨⟨w, rfl⟩, hnil⟩
  cases hnil
  exact ⟨w, rfl⟩

theorem res_nil {res : List Val} (h : List.Forall₂ ScalarType.HasVal [] res) : res = [] :=
  List.forall₂_nil_left_iff.1 h

/-! ## Executable equality on a larger instruction fragment -/

mutual
/-- Structural equality on the instructions used by the checkers; `false` elsewhere. -/
def ieqG : Instr → Instr → Bool
  | .return_, .return_ => true
  | .drop, .drop => true
  | .loop bt b, .loop bt' b' => bt == bt' && ieqsG b b'
  | .block bt b, .block bt' b' => bt == bt' && ieqsG b b'
  | .if_ bt t e, .if_ bt' t' e' => bt == bt' && ieqsG t t' && ieqsG e e'
  | .br l, .br l' => l == l'
  | .brIf l, .brIf l' => l == l'
  | .call f, .call f' => f == f'
  | .localGet x, .localGet x' | .localSet x, .localSet x' => x == x'
  | .intConst t b, .intConst t' b' => t == t' && b.toNat == b'.toNat
  | .intTestOp t o, .intTestOp t' o' => t == t' && o == o'
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | .intBinOp t o, .intBinOp t' o' => t == t' && o == o'
  | _, _ => false
/-- `ieqG` on lists. -/
def ieqsG : List Instr → List Instr → Bool
  | [], [] => true
  | i :: is, i' :: is' => ieqG i i' && ieqsG is is'
  | _, _ => false
end

theorem ieqsG_sound_of {b b' : List Instr} (h : ieqsG b b' = true)
    (ih : ∀ j ∈ b, ∀ j', ieqG j j' = true → j = j') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons j' js' => unfold ieqsG at h; simp at h
  | cons j js ihl =>
    cases b' with
    | nil => unfold ieqsG at h; simp at h
    | cons j' js' =>
      unfold ieqsG at h
      simp only [Bool.and_eq_true] at h
      rw [ih j (by simp) j' h.1, ihl h.2 (fun k hk => ih k (by simp [hk]))]

theorem ieqG_sound_lt : ∀ (n : Nat) (i i' : Instr), sizeOf i < n → ieqG i i' = true → i = i'
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, i, i', hs, h => by
    have hlist : ∀ b b' : List Instr, sizeOf b < n → ieqsG b b' = true → b = b' :=
      fun b _ hb hbb => ieqsG_sound_of hbb fun j hj j' =>
        ieqG_sound_lt n j j' (by have := List.sizeOf_lt_of_mem hj; omega)
    unfold ieqG at h
    split at h
    all_goals (try simp only [Bool.and_eq_true, beq_iff_eq] at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (simp at h; done)
      | (obtain ⟨⟨rfl, h2⟩, h3⟩ := h; simp only [Instr.if_.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2, hlist _ _ (by omega) h3])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.loop.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.block.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; rw [BitVec.eq_of_toNat_eq h2])
      | (obtain ⟨rfl, -⟩ := h; cases ‹IntTestOp›; cases ‹IntTestOp›; rfl)

theorem ieqsG_sound {is is' : List Instr} (h : ieqsG is is' = true) : is = is' :=
  ieqsG_sound_of h fun _ _ _ => ieqG_sound_lt _ _ _ (Nat.lt_succ_self _)

/-! ## The shape of an instantiated module -/

/-- A host stub for import `k`, with `n` parameters. -/
def stubOkN (k n : Nat) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .host k' => k' == k
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps _) => ps.length == n
    | _ => false)

/-- The exported function: its locals, body and type, in a module instance whose functions
are `mf`. -/
def fnOkN (np nr : Nat) (mf : List Nat) (locals : List ValType) (body : List Instr)
    (D : List (Option Val)) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm c => c.locals == locals && ieqsG c.body body
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == np && rs.length == nr
    | _ => false) &&
  fi.module.funcs == mf &&
  locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) == D

/-- The shape of an instantiated module with imports `fts` and one export of type `eft`, the
function right after the import stubs (checked by kernel evaluation). -/
def gshapeOk (I : ScalarInstance) (fts : List FnType) (eft : FnType) (locals : List ValType)
    (body : List Instr) (D : List (Option Val)) : Bool :=
  I.imports == fts && I.exports == [eft] && I.addrs == [fts.length] &&
  (List.range fts.length).all (fun k => match I.store.funcs[k]?, fts[k]? with
    | some fk, some ft => stubOkN k ft.params.length fk
    | _, _ => false) &&
  match I.store.funcs[fts.length]? with
  | some fi => fnOkN eft.params.length eft.results.length (List.range (fts.length + 1)) locals
      body D fi
  | none => false

/-- The shape of an instantiated module with imports `fts` and one export of type `eft`. -/
structure GShape (I : ScalarInstance) (fts : List FnType) (eft : FnType) (locals : List ValType)
    (body : List Instr) (D : List (Option Val)) : Prop where
  imports : I.imports = fts
  exports : I.exports = [eft]
  addr : ∀ j, I.addr j = fts.length
  stub : ∀ k (hk : k < fts.length), ∃ (fk : FuncInst Nat) (ps rs : Ty (.list .val)),
    I.store.funcs[k]? = some fk ∧ fk.code = .host k ∧ Expand fk.type (.func ps rs) ∧
    ps.length = (fts[k]'hk).params.length
  fn : ∃ (fi : FuncInst Nat) (code : Func) (ps rs : Ty (.list .val)),
    I.store.funcs[fts.length]? = some fi ∧ fi.code = .wasm code ∧ code.locals = locals ∧
    code.body = body ∧ Expand fi.type (.func ps rs) ∧ ps.length = eft.params.length ∧
    rs.length = eft.results.length ∧ fi.module.funcs = List.range (fts.length + 1) ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D

theorem stubOkN_spec {k n : Nat} {fi : FuncInst Nat} (h : stubOkN k n fi = true) :
    ∃ ps rs, fi.code = .host k ∧ Expand fi.type (.func ps rs) ∧ ps.length = n := by
  unfold stubOkN at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  split at h₁
  · rename_i k' hc
    split at h₂
    · rename_i ps rs he
      exact ⟨ps, rs, by rw [hc, beq_iff_eq.1 h₁], Expand.iff.2 he, beq_iff_eq.1 h₂⟩
    · cases h₂
  · cases h₁

theorem fnOkN_spec {np nr : Nat} {mf : List Nat} {locals : List ValType} {body : List Instr}
    {D : List (Option Val)} {fi : FuncInst Nat} (h : fnOkN np nr mf locals body D fi = true) :
    ∃ (code : Func) (ps rs : Ty (.list .val)),
    fi.code = .wasm code ∧ code.locals = locals ∧ code.body = body ∧
    Expand fi.type (.func ps rs) ∧ ps.length = np ∧ rs.length = nr ∧ fi.module.funcs = mf ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D := by
  unfold fnOkN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  split at h₁
  · rename_i c hc
    split at h₂
    · rename_i ps rs he
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁ h₂ h₃ h₄
      exact ⟨c, ps, rs, hc, h₁.1, ieqsG_sound h₁.2, Expand.iff.2 he, h₂.1, h₂.2, h₃, h₄⟩
    · cases h₂
  · cases h₁

theorem GShape.of_ok {I : ScalarInstance} {fts : List FnType} {eft : FnType}
    {locals : List ValType} {body : List Instr} {D : List (Option Val)}
    (h : gshapeOk I fts eft locals body D = true) : GShape I fts eft locals body D := by
  unfold gshapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hi, he⟩, ha⟩, hst⟩, hf⟩ := h
  refine ⟨hi, he, fun j => ?_, fun k hk => ?_, ?_⟩
  · have hl : I.exports.length = 1 := by rw [he]; rfl
    have hj : j.val = 0 := by have := j.2; omega
    simp [ScalarInstance.addr, ha, hj]
  · have hk' := List.all_eq_true.1 hst k (List.mem_range.2 hk)
    rw [List.getElem?_eq_getElem hk] at hk'
    split at hk'
    · rename_i fk ft hfk hft
      obtain rfl := Option.some.inj hft
      obtain ⟨ps, rs, h⟩ := stubOkN_spec hk'
      exact ⟨fk, ps, rs, hfk, h⟩
    · cases hk'
  · split at hf
    · rename_i fi hfi
      obtain ⟨c, ps, rs, h⟩ := fnOkN_spec hf
      exact ⟨fi, c, ps, rs, hfi, h⟩
    · cases hf

/-! ## Import calls of an instantiated module -/

section Calls

variable {I : ScalarInstance} {fts : List FnType} {eft : FnType} {locals : List ValType}
  {body : List Instr} {D : List (Option Val)}
  (hS : GShape I fts eft locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (fts.length + 1)) {Ii : ISpec I.E}

include hS hs hm

/-- A call of import `k` by an instantiated module of shape `GShape`. -/
theorem X.callG {k : Nat} (hk : k < fts.length) {x : FuncIdx} (hx : x.toNat = k)
    {args : List Val} (hargs : (fts[k]'hk).params.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ Ii.pre e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Leaves Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ args) ++ expression (.call x :: is)) Q := by
  obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
  refine hwp_importN (fk := fk) (ps := ps) (rs := rs) ?_ (by rw [hs]; exact hf) hcode he
    (hps.trans hargs) hop hc hQ
  rw [hm, hx, List.getElem?_range (by omega)]

end Calls

/-! ## From the function body to the game -/

/-- **A module of shape `GShape` meets its specification** for the trivial export
specification if its body does, from the frame of a call on any typed arguments, for every
postcondition accepting returns, traps, exceptions and the normal end. -/
theorem gameSat_ofG {I : ScalarInstance} {fts : List FnType} {eft : FnType}
    {locals : List ValType} {body : List Instr} {D : List (Option Val)}
    (hS : GShape I fts eft locals body D) (hr : eft.results = []) {Ii : ISpec I.E}
    (hbody : ∀ (fi : FuncInst Nat) (s : Store Nat) (args : List Val) (Q : Post Nat),
      List.Forall₂ ScalarType.HasVal eft.params args →
      I.store.funcs[fts.length]? = some fi → fi.module.funcs = List.range (fts.length + 1) →
      s.funcs = I.store.funcs → Leaves Q s → (∀ f, Q s f (.normal [])) →
      HWP P (gameHost I Ii) s ⟨args.map some ++ D, fi.module⟩ (vals [] ++ expression body) Q) :
    GameSat P I (StoreInv I) Ii (topISpec _) := by
  intro j
  rw [hS.addr j]
  obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := hS.fn
  have hl : I.exports.length = 1 := by rw [hS.exports]; rfl
  have hg : I.exports.get j = eft := by
    rw [List.get_eq_getElem, List.getElem_of_eq hS.exports j.2]
    have hj : j.val = 0 := by have := j.2; omega
    simp only [hj]
    rfl
  have hrs0 : rs.length = 0 := by rw [hrs, hr]; rfl
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fi := fi) (fun s args hpre => by rw [hpre.1]; exact hf) hcode he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨-, ht, -⟩ := hpre
      rw [hg] at ht
      rw [hps, ht.length_eq]
    · obtain ⟨hInv, ht, -⟩ := hpre
      have ht' := ht
      rw [hg] at ht'
      have hfr : Frame.forCall fi.module args code.locals = ⟨args.map some ++ D, fi.module⟩ := by
        unfold Frame.forCall
        rw [hloc, hD]
      rw [hfr, hbod]
      have hR : ∀ o, (exportSpec I (StoreInv I) (topISpec _) j).post s args s o :=
        fun _ => ⟨hInv, fun _ _ _ => trivial⟩
      refine hbody fi s args _ ht' hf hm hInv
        (leaves_body hrs0 hInv (fun _ _ => trivial)) (fun F => ?_) n
      exact ⟨by simp [hrs0], rfl, .inl ⟨[], by simp, hR _⟩⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
