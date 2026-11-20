module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.OneShot
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.TwoWords
public import Silmaril.Wasm.Logic.Exec.Thms

/-!
# Proofs: modules with several exports and globals, and stateful specifications

* `MShape I fts efts fns mg`: an instantiated module with imports `fts` (host stubs at addresses
  `0, …`), exports `efts` implemented, in order, by the functions right after the stubs, with
  locals, bodies and default locals `fns`, in a module instance whose globals are at `mg`;
  checked by kernel evaluation of `mshapeOk` (`MShape.of_ok`);
* `X.globalGet`, `X.globalSet`: the global
  rules (through `Silmaril.Wasm.Examples.Common.Wp.exec1`);
* `X.callM`, `X.wWordM`, `X.wNilM`, `X.wConsM`: import calls (cons writer calls) for a
  postcondition accepting traps and exceptions;
* `sgameSat_ofM`: the body-to-`SGameSat` step for a stateful specification whose invariant
  determines the ghost state: each body, from a store representing `g`, must accept traps and
  exceptions in every store representing `g` (no answer, no event: the ghost state stays), and
  return results only when the answers they denote meet `post g` and end in a store representing
  `next g`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-! ## Executable instruction equality, with globals -/

mutual
/-- Structural equality on the instructions of `ieqG`, the global instructions, `unreachable`
and the integer loads and stores; `false` elsewhere. -/
def ieqM : Instr → Instr → Bool
  | .return_, .return_ => true
  | .drop, .drop => true
  | .loop bt b, .loop bt' b' => bt == bt' && ieqsM b b'
  | .block bt b, .block bt' b' => bt == bt' && ieqsM b b'
  | .if_ bt t e, .if_ bt' t' e' => bt == bt' && ieqsM t t' && ieqsM e e'
  | .br l, .br l' => l == l'
  | .brIf l, .brIf l' => l == l'
  | .call f, .call f' => f == f'
  | .localGet x, .localGet x' | .localSet x, .localSet x' => x == x'
  | .globalGet x, .globalGet x' | .globalSet x, .globalSet x' => x == x'
  | .intConst t b, .intConst t' b' => t == t' && b.toNat == b'.toNat
  | .intTestOp t o, .intTestOp t' o' => t == t' && o == o'
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | .intBinOp t o, .intBinOp t' o' => t == t' && o == o'
  | .unreachable, .unreachable => true
  | .intStore t p x a, .intStore t' p' x' a' => t == t' && p == p' && x == x' && a == a'
  | .intLoad t p x a, .intLoad t' p' x' a' => t == t' && p == p' && x == x' && a == a'
  | _, _ => false
/-- `ieqM` on lists. -/
def ieqsM : List Instr → List Instr → Bool
  | [], [] => true
  | i :: is, i' :: is' => ieqM i i' && ieqsM is is'
  | _, _ => false
end

theorem ieqsM_sound_of {b b' : List Instr} (h : ieqsM b b' = true)
    (ih : ∀ j ∈ b, ∀ j', ieqM j j' = true → j = j') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons j' js' => unfold ieqsM at h; simp at h
  | cons j js ihl =>
    cases b' with
    | nil => unfold ieqsM at h; simp at h
    | cons j' js' =>
      unfold ieqsM at h
      simp only [Bool.and_eq_true] at h
      rw [ih j (by simp) j' h.1, ihl h.2 (fun k hk => ih k (by simp [hk]))]

theorem ieqM_sound_lt : ∀ (n : Nat) (i i' : Instr), sizeOf i < n → ieqM i i' = true → i = i'
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, i, i', hs, h => by
    have hlist : ∀ b b' : List Instr, sizeOf b < n → ieqsM b b' = true → b = b' :=
      fun b _ hb hbb => ieqsM_sound_of hbb fun j hj j' =>
        ieqM_sound_lt n j j' (by have := List.sizeOf_lt_of_mem hj; omega)
    unfold ieqM at h
    split at h
    all_goals (try simp only [Bool.and_eq_true, beq_iff_eq] at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl)
      | (simp at h; done)
      | (obtain ⟨⟨rfl, h2⟩, h3⟩ := h; simp only [Instr.if_.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2, hlist _ _ (by omega) h3])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.loop.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.block.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; rw [BitVec.eq_of_toNat_eq h2])
      | (obtain ⟨rfl, -⟩ := h; cases ‹IntTestOp›; cases ‹IntTestOp›; rfl)

theorem ieqsM_sound {is is' : List Instr} (h : ieqsM is is' = true) : is = is' :=
  ieqsM_sound_of h fun _ _ _ => ieqM_sound_lt _ _ _ (Nat.lt_succ_self _)

/-- The exported function: its locals, body and type, in a module instance whose functions
are `mf` (`fnOkN` with `ieqsM`). -/
def fnOkM (np nr : Nat) (mf : List Nat) (locals : List ValType) (body : List Instr)
    (D : List (Option Val)) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm c => c.locals == locals && ieqsM c.body body
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == np && rs.length == nr
    | _ => false) &&
  fi.module.funcs == mf &&
  locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) == D

theorem fnOkM_spec {np nr : Nat} {mf : List Nat} {locals : List ValType} {body : List Instr}
    {D : List (Option Val)} {fi : FuncInst Nat} (h : fnOkM np nr mf locals body D fi = true) :
    ∃ (code : Func) (ps rs : Ty (.list .val)),
    fi.code = .wasm code ∧ code.locals = locals ∧ code.body = body ∧
    Expand fi.type (.func ps rs) ∧ ps.length = np ∧ rs.length = nr ∧ fi.module.funcs = mf ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D := by
  unfold fnOkM at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  split at h₁
  · rename_i c hc
    split at h₂
    · rename_i ps rs he
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁ h₂ h₃ h₄
      exact ⟨c, ps, rs, hc, h₁.1, ieqsM_sound h₁.2, Expand.iff.2 he, h₂.1, h₂.2, h₃, h₄⟩
    · cases h₂
  · cases h₁

/-! ## The shape of a module with several exports -/

/-- The shape of an instantiated module, by kernel evaluation. -/
def mshapeOk (I : ScalarInstance) (fts efts : List FnType)
    (fns : List (List ValType × List Instr × List (Option Val))) (mg : List Nat) : Bool :=
  I.imports == fts && I.exports == efts &&
  I.addrs == (List.range efts.length).map (fts.length + ·) && fns.length == efts.length &&
  (List.range fts.length).all (fun k => match I.store.funcs[k]?, fts[k]? with
    | some fk, some ft => stubOkN k ft.params.length fk
    | _, _ => false) &&
  (List.range efts.length).all (fun j => match I.store.funcs[fts.length + j]?, efts[j]?, fns[j]? with
    | some fi, some eft, some (locals, body, D) =>
      fnOkM eft.params.length eft.results.length (List.range (fts.length + efts.length)) locals
        body D fi && fi.module.globals == mg
    | _, _, _ => false)

/-- **The shape of an instantiated module** with imports `fts` and exports `efts`. -/
structure MShape (I : ScalarInstance) (fts efts : List FnType)
    (fns : List (List ValType × List Instr × List (Option Val))) (mg : List Nat) : Prop where
  imports : I.imports = fts
  exports : I.exports = efts
  addrs : I.addrs = (List.range efts.length).map (fts.length + ·)
  len : fns.length = efts.length
  stub : ∀ k (hk : k < fts.length), ∃ (fk : FuncInst Nat) (ps rs : Ty (.list .val)),
    I.store.funcs[k]? = some fk ∧ fk.code = .host k ∧ Expand fk.type (.func ps rs) ∧
    ps.length = (fts[k]'hk).params.length
  fn : ∀ j (hj : j < efts.length), ∃ (fi : FuncInst Nat) (code : Func) (ps rs : Ty (.list .val)),
    I.store.funcs[fts.length + j]? = some fi ∧ fi.code = .wasm code ∧
    code.locals = (fns[j]'(by omega)).1 ∧ code.body = (fns[j]'(by omega)).2.1 ∧
    Expand fi.type (.func ps rs) ∧ ps.length = (efts[j]'hj).params.length ∧
    rs.length = (efts[j]'hj).results.length ∧
    fi.module.funcs = List.range (fts.length + efts.length) ∧ fi.module.globals = mg ∧
    (fns[j]'(by omega)).1.map (fun t => defaultVal? ((liftVal t).substAll
      (fi.module.types.map .dt))) = (fns[j]'(by omega)).2.2

theorem MShape.of_ok {I : ScalarInstance} {fts efts : List FnType}
    {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
    (h : mshapeOk I fts efts fns mg = true) : MShape I fts efts fns mg := by
  unfold mshapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hi, he⟩, ha⟩, hl⟩, hst⟩, hf⟩ := h
  refine ⟨hi, he, ha, hl, fun k hk => ?_, fun j hj => ?_⟩
  · have hk' := List.all_eq_true.1 hst k (List.mem_range.2 hk)
    rw [List.getElem?_eq_getElem hk] at hk'
    split at hk'
    · rename_i fk ft hfk hft
      obtain rfl := Option.some.inj hft
      obtain ⟨ps, rs, h⟩ := stubOkN_spec hk'
      exact ⟨fk, ps, rs, hfk, h⟩
    · cases hk'
  · have hj' := List.all_eq_true.1 hf j (List.mem_range.2 hj)
    have hjf : j < fns.length := by rw [hl]; exact hj
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjf] at hj'
    split at hj'
    · rename_i fi eft locals body D hfi heft hfns
      obtain rfl := Option.some.inj heft
      have hfns' := Option.some.inj hfns
      simp only [Bool.and_eq_true, beq_iff_eq] at hj'
      obtain ⟨c, ps, rs, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := fnOkM_spec hj'.1
      refine ⟨fi, c, ps, rs, hfi, h₁, ?_, ?_, h₄, h₅, h₆, h₇, hj'.2, ?_⟩
      · rw [hfns']; exact h₂
      · rw [hfns']; exact h₃
      · rw [hfns']; exact h₈
    · cases hj'

theorem MShape.addr {I : ScalarInstance} {fts efts : List FnType}
    {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
    (hS : MShape I fts efts fns mg) (j : Fin I.exports.length) :
    I.addr j = fts.length + j.val := by
  have hj : j.val < efts.length := hS.exports ▸ j.2
  simp [ScalarInstance.addr, hS.addrs, List.getD_eq_getElem?_getD, hj]

theorem MShape.lt_fns {I : ScalarInstance} {fts efts : List FnType}
    {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
    (hS : MShape I fts efts fns mg) (j : Fin I.exports.length) : j.val < fns.length := by
  have h₁ : j.val < I.exports.length := j.2
  have h₂ : I.exports.length = fns.length := by rw [hS.exports, hS.len]
  omega

theorem MShape.get {I : ScalarInstance} {fts efts : List FnType}
    {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
    (hS : MShape I fts efts fns mg) (j : Fin I.exports.length) :
    I.exports.get j = efts[j.val]'(hS.exports ▸ j.2) := by
  rw [List.get_eq_getElem]
  exact List.getElem_of_eq hS.exports j.2

/-! ## Globals -/

theorem gval_setGlobal (s : Store Nat) (a b : Nat) (v : Val) :
    gval (s.setGlobal a v) b = if a = b then (gval s b).map (fun _ => v) else gval s b := by
  unfold gval Store.setGlobal
  simp only [List.getElem?_modify]
  split_ifs with h
  · subst h
    cases s.globals[a]? <;> rfl
  · simp

@[simp] theorem setGlobal_funcs (s : Store Nat) (a : Nat) (v : Val) :
    (s.setGlobal a v).funcs = s.funcs := rfl

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

theorem X.globalGet {x : GlobalIdx} {a : Nat} {v : Val}
    (hx : f.module.globals[x.toNat]? = some a) (hv : gval s a = some v)
    (h : HWP P host s f (vals (us ++ [v]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.globalGet x :: is)) Q := by
  obtain ⟨gi, hgi, rfl⟩ : ∃ gi, s.globals[a]? = some gi ∧ gi.value = v := by
    unfold gval at hv
    cases hg : s.globals[a]? with
    | none => simp [hg] at hv
    | some gi => simp only [hg, Option.map_some, Option.some.injEq] at hv; exact ⟨gi, rfl, hv⟩
  have h₁ := Silmaril.Wasm.Examples.Common.Wp.exec1 (m := .part) (P := P) (host := host)
    (s := s) (f := f) (rs := us.reverse) (rest := expression is) (Q := Q) (i := .globalGet x) (s' := s) (f' := f)
    (rs' := gi.value :: us.reverse)
    (by simp [Silmaril.Wasm.Logic.Core.exec1, Store.global?, hx, hgi])
    (by simpa using h)
  simpa [expression] using h₁

theorem X.globalSet {x : GlobalIdx} {a : Nat} {v : Val}
    (hx : f.module.globals[x.toNat]? = some a) (ha : (gval s a).isSome)
    (h : HWP P host (s.setGlobal a v) f (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [v]) ++ expression (.globalSet x :: is)) Q := by
  obtain ⟨gi, hgi⟩ : ∃ gi, s.globals[a]? = some gi := by
    unfold gval at ha
    cases hg : s.globals[a]? with
    | none => simp [hg] at ha
    | some gi => exact ⟨gi, rfl⟩
  have h₁ := Silmaril.Wasm.Examples.Common.Wp.exec1 (m := .part) (P := P) (host := host)
    (s := s) (f := f) (rs := v :: us.reverse) (rest := expression is) (Q := Q) (i := .globalSet x)
    (s' := s.setGlobal a v) (f' := f) (rs' := us.reverse)
    (by simp [Silmaril.Wasm.Logic.Core.exec1, Store.global?, hx, hgi, Silmaril.Wasm.Logic.Core.popV])
    (by simpa using h)
  simpa [expression] using h₁

theorem Traps.label {rest : List Admin} (h : Traps Q s) :
    Traps (labelPost P host 0 [] us (seqPost P host rest Q)) s := fun f =>
  ⟨(h f).1, (h f).2⟩

/-! ## Import calls -/

section Calls

variable {I : ScalarInstance} {fts efts : List FnType}
  {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
  (hS : MShape I fts efts fns mg) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (fts.length + efts.length)) {Ii : ISpec I.E}

include hS hs hm

/-- A call of import `k` by a module of shape `MShape`, for a postcondition accepting traps and
exceptions. -/
theorem X.callM {k : Nat} (hk : k < fts.length) {x : FuncIdx} (hx : x.toNat = k)
    {args : List Val} (hargs : (fts[k]'hk).params.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ Ii.pre e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Traps Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ args) ++ expression (.call x :: is)) Q := by
  obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
  refine hwp_importT (fk := fk) (ps := ps) (rs := rs) ?_ (by rw [hs]; exact hf) hcode he
    (hps.trans hargs) hop hc hQ
  rw [hm, hx, List.getElem?_range (by omega)]

end Calls

section Writers

variable {I : ScalarInstance} {efts : List FnType}
  {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
  (hS : MShape I twoFTs efts fns mg) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (twoFTs.length + efts.length))
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hS hs hm

/-- `word(x)`. -/
theorem X.wWordM {x : BitVec 64} (hQ : Traps Q s)
    (hc : ∀ r, ρ r = some (.atom x) →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i64 x]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.callM hS hs hm (k := 2) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨x, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wWord_post hS.imports he hv hr
      exact hc r h) hQ

/-- `nil()`. -/
theorem X.wNilM (hQ : Traps Q s)
    (hc : ∀ r, ρ r = some .nil →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f (vals us ++ expression (.call ⟨0⟩ :: is)) Q := by
  have h := X.callM (us := us) (args := []) (x := ⟨0⟩) hS hs hm (k := 0) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) .nil)
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wNil_post hS.imports he hv hr
      exact hc r h) hQ
  simpa using h

/-- `cons(a, b)`. -/
theorem X.wConsM {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = some x)
    (hb : ρ b = some y) (hQ : Traps Q s)
    (hc : ∀ r, ρ r = some (.cons x y) →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i32 a] ++ [.i32 b]) ++ expression (.call ⟨1⟩ :: is)) Q := by
  rw [List.append_assoc]
  exact X.callM hS hs hm (k := 1) (args := [.i32 a, .i32 b]) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ (.cons ⟨b, rfl⟩ .nil)))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wCons_post hS.imports ha hb he hv hr
      exact hc r h) hQ

end Writers

/-! ## From the function bodies to the game -/

/-- **A module of shape `MShape` meets a stateful specification** whose invariant determines the
ghost state and whose answers without values (traps, exceptions) are allowed and keep the ghost
state, if each body, from a store representing `g`, accepts traps and exceptions in every store
representing `g` and returns results only when their answers meet `post g` and end in a store
representing `next g`. -/
theorem sgameSat_ofM {I : ScalarInstance} {fts efts : List FnType}
    {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
    (hS : MShape I fts efts fns mg) {Ii : ISpec I.E} {G : Type} {S : SSpec I G}
    (hinv : ∀ g s, S.inv g s → s.funcs = I.store.funcs)
    (huniq : ∀ g g' s, S.inv g s → S.inv g' s → g = g')
    (hIe : ∀ g (f : I.F.Op) (v : I.F.Ar f), ansVals v = none → S.post g f v ∧ S.next g f v = g)
    (hbody : ∀ (j : Fin I.exports.length) (fi : FuncInst Nat) (s : Store Nat) (args : List Val)
      (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args) (g : G) (Q : Post Nat),
      I.store.funcs[fts.length + j.val]? = some fi →
      fi.module.funcs = List.range (fts.length + efts.length) → fi.module.globals = mg →
      S.inv g s → (∀ s', S.inv g s' → Traps Q s') →
      (∀ s' f res, res.length = (I.exports.get j).results.length →
        (∀ v : Answer (I.exports.get j), v.toResult = .values res →
          S.post g ⟨j, ⟨args, ht⟩⟩ v ∧ S.inv (S.next g ⟨j, ⟨args, ht⟩⟩ v) s') →
        Q s' f (.ret res)) →
      HWP P (gameHost I Ii) s
        ⟨args.map some ++ (fns[j.val]'(hS.lt_fns j)).2.2, fi.module⟩
        (vals [] ++ expression (fns[j.val]'(hS.lt_fns j)).2.1)
        Q) :
    SGameSat P I Ii S := by
  intro j
  rw [hS.addr j]
  have hj : j.val < efts.length := hS.exports ▸ j.2
  obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hmg, hD⟩ := hS.fn j hj
  have hg := hS.get j
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fi := fi) (fun s args hpre => by
        obtain ⟨⟨g, hi⟩, -⟩ := hpre
        rw [hinv g s hi]; exact hf) hcode he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨-, ht⟩ := hpre
      rw [hg] at ht
      rw [hps, ht.length_eq]
    · obtain ⟨⟨g, hInv⟩, ht⟩ := hpre
      have hfr : Frame.forCall fi.module args code.locals =
          ⟨args.map some ++ (fns[j.val]'(hS.lt_fns j)).2.2, fi.module⟩ := by
        unfold Frame.forCall
        rw [hloc, hD]
      rw [hfr, hbod]
      have hpost_none : ∀ s', S.inv g s' → ∀ o, (∀ v : Answer (I.exports.get j),
          resultOutcome v.toResult = o → ansVals v = none) →
          (sexportSpec I S j).post s args s' o := by
        intro s' hs' o hno g' hg' ht₂ v hv
        obtain rfl := huniq g g' s hInv hg'
        have := hIe g ⟨j, ⟨args, ht₂⟩⟩ v (hno v hv)
        exact ⟨this.1, by rw [this.2]; exact hs'⟩
      refine hbody j fi s args ht g _ hf hm hmg hInv (fun s' hs' F => ⟨?_, fun a => ?_⟩)
        (fun s' F res hlen hpost => ?_) n
      · refine ⟨rfl, .inr (.inl ⟨rfl, hpost_none s' hs' _ fun v hv => ?_⟩)⟩
        cases v with
        | values vs => simp [Answer.toResult, resultOutcome] at hv
        | _ => rfl
      · refine ⟨rfl, .inr (.inr ⟨a, rfl, hpost_none s' hs' _ fun v hv => ?_⟩)⟩
        cases v with
        | values vs => simp [Answer.toResult, resultOutcome] at hv
        | _ => rfl
      · refine ⟨[], res, by simp, by rw [hlen, hrs, hg], rfl, .inl ⟨res, rfl, ?_⟩⟩
        intro g' hg' ht₂ v hv
        obtain rfl := huniq g g' s hInv hg'
        refine hpost v ?_
        cases v with
        | values vs => simpa [Answer.toResult, resultOutcome] using hv
        | _ => simp [Answer.toResult, resultOutcome] at hv

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
