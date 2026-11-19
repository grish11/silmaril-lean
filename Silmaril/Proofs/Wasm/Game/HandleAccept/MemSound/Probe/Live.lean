module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.Sound
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Live

/-!
# Proofs: the probe reader accepts the trees its host describes

Against `probeEnv c w` (`next` returns `c`; `leaf` writes the words `8, 2, w, w` at `[0, 16)`
of memory `0`), the traced session of `probeMod d.ix` invokes `check(h)` and runs:
`next(h, 0)` (decoded as `read (q₂ h 0) (a₂ c)`), `leaf(c, 0)` (decoded from the memory after
its answer as `read (q₃ c) a`, where `a` is what `a₃` reads on every page the host wrote) and
`accept(h)` (`probe_traces`). In a fixed environment of `Rhos` where both reads are valid and
correct and `h` denotes `t`, the session accepts `t` (`probe_live_of`).

Payload facts on the written page: `bytesPay dec` reads `dec [b₀, b₁]` when `w = symWord b₀ b₁`
(`bytesPay_page`); `u64Pay` reads `u64Page = 8 + 2 * 2 ^ 32` (`u64Pay_page`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Text Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Probe
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Items
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers
open Silmaril.Wasm.Logic.Core (bytesAt leNat)

variable {Qy An Y α : Type}

/-! ## Instance facts -/

/-- The spec instance exists, its memory is one page, and the parameter of `check` is an
`i32`. -/
def probeLiveOk (ix : ProbeImports) : Bool :=
  (Silmaril.Wasm.Verify.specInstance? (probeMod ix)).isSome &&
  memSizes (probeMod ix) == [65536] &&
  match prep (probeMod ix) with
  | some (c, _) =>
    match c.store.funcs[3]? with
    | some fi =>
      match fi.type.expand? with
      | some (.func ps _) => decide (ps.toList = [.num (.int .i32)])
      | _ => false
    | none => false
  | none => false

theorem probe_live_facts {ix : ProbeImports} (hok : probeLiveOk ix = true) :
    (Silmaril.Wasm.Verify.specInstance? (probeMod ix)).isSome = true ∧
    memSizes (probeMod ix) = [65536] ∧
    ∀ {c : Config Nat} {st : Option FuncIdx}, prep (probeMod ix) = some (c, st) →
      ∀ {fi : FuncInst Nat}, c.store.funcs[3]? = some fi → ∀ {ps rs : Ty (.list .val)},
        Expand fi.type (.func ps rs) → ps.toList = [.num (.int .i32)] := by
  unfold probeLiveOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  refine ⟨h1, h2, ?_⟩
  intro c st hp fi hf ps rs he
  rw [hp] at h3
  simp only [hf, Expand.iff.1 he] at h3
  exact of_decide_eq_true h3

/-- The `probeEnv` replies are admitted by `probeReply`. -/
theorem probeEnv_reply (c w : BitVec 32) (s : Store Nat) :
    ReplyEnvs probeReply s (probeEnv c w) := by
  rintro q e a q' rfl
  by_cases h0 : e.target = 0
  · simp only [h0, ↓reduceIte]
    refine ⟨⟨rfl, rfl⟩, fun vs hv => ?_⟩
    cases hv
    exact ⟨fun _ => ⟨c, rfl⟩, fun h => by omega⟩
  · simp only [h0, ↓reduceIte]
    refine ⟨?_, fun vs hv => ?_⟩
    · by_cases h1 : e.target = 1
      · simp only [h1, ↓reduceIte]
        exact itemsStore_keeps w w e.store
      · simp only [h1, ↓reduceIte]
        exact ⟨rfl, rfl⟩
    · cases hv
      exact ⟨fun h => absurd h h0, fun _ => rfl⟩

/-! ## The session -/

/-- **The reader trace of the session**, for a decoder whose `leaf` answer on every page the
host wrote is `a`. -/
theorem probe_traces (P : Profile) {d : ProbeDec Qy An} (hok : probeOk d.ix = true)
    (hlive : probeLiveOk d.ix = true) (h c w : BitVec 32) {a : An}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      d.a₃ ⟨.values [], some B'⟩ 0 = a) :
    [.enter, .read (d.q₂ h 0) (d.a₂ c), .read (d.q₃ c) a, .accept h] ∈
      probeTraces P (ReplyEnvs probeReply) 0 (probeMod d.ix) d := by
  obtain ⟨hspec, hmem, hparam⟩ := probe_live_facts hlive
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists hspec
  obtain ⟨cf, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨hne, rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ :=
    probe_facts hok hp
  obtain ⟨mi, hmis, hsize⟩ := one_page hmem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, -, -⟩ := fnOk_spec h3
  rw [show cf.withStart none = cf from rfl] at hI
  have hmem0 : cf.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = cf.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ ∧ s.funcs[3]? = some f₃ := by
    intro s hs; rw [hs, hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hmi : cf.store.mems[0]? = some mi := by rw [hmis]; rfl
  have hpar := hparam hp (hfs _ rfl).2.2.2 he
  let L := probeEnv c w
  let R := probeRoles d
  have t₀ : TSession P L (probeMod d.ix) (some 0) R cf () Is.addrs .inst false (cf, ()) [] :=
    .start
  have hok' : InvokeOk cf.store 3 [.i32 h] := ⟨f₃, ps, rs, (hfs _ rfl).2.2.2, he, by
    rw [hpar]; exact .cons (.num _) .nil⟩
  have ha : 3 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok'
  -- enter `check(h)`
  have st₀ : Step P NH (invoke cf.store 3 [.i32 h])
      ⟨cf.store, {}, [.frame 0 (Frame.forCall f₃.module [.i32 h] code.locals)
        [.label 0 [] (expression probeBody)]]⟩ := by
    have hst := Step.callRefFunc (P := P) (host := NH) (s := cf.store) (f := {})
      (c := .callRefType ((cf.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [.i32 h])
      (a := 3) (fi := f₃) (code := code) trivial (hfs _ rfl).2.2.2 he (by rw [hps]; rfl) hcode3
    rw [hrs, hbody] at hst
    exact hst
  have hFf : (Frame.forCall f₃.module [.i32 h] code.locals).module.funcs = [0, 1, 2, 3] := by
    simp [Frame.forCall, hfuncs]
  have hFl : (Frame.forCall f₃.module [.i32 h] code.locals).locals = [some (.i32 h)] := by
    unfold Frame.forCall
    dsimp only
    rw [hloc]
    rfl
  generalize Frame.forCall f₃.module [.i32 h] code.locals = F at st₀ hFf hFl
  have hv : F.local? ⟨0⟩ = some (some (.i32 h)) := by simp [Frame.local?, hFl, Idx.toNat]
  -- next(h, 0)
  have st₁ : Step P NH ⟨cf.store, {}, [.frame 0 F [.label 0 [] (expression probeBody)]]⟩
      ⟨cf.store, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (probeBody.drop 1))]]⟩ :=
    step_body (step_mid [] (expression (probeBody.drop 1)) (step_localGet hv))
  have st₂ : Step P NH ⟨cf.store, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [(Val.i32 h).toAdmin] ++ expression (probeBody.drop 1))]]⟩
      ⟨cf.store, {}, (bodyCtx F (expression (probeBody.drop 3))).fill
        (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 h, .i32 0] (expression (probeBody.drop 3))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs _ rfl).1))
  have hd₁ : decompose? cf.store ((bodyCtx F (expression (probeBody.drop 3))).fill
      (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (probeBody.drop 3)), 0, 0, [.i32 h, .i32 0]) :=
    decompose_fill _ trivial (hfs _ rfl).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨cf.store, .values [.i32 c]⟩) (q' := ())
    (by show _ = _; rfl)
  -- leaf(c, 0)
  have st₃ : Step P NH ⟨cf.store, {}, (bodyCtx F (expression (probeBody.drop 3))).fill
      (Result.values [.i32 c]).toAdmin⟩
      ⟨cf.store, {}, (bodyCtx F (expression (probeBody.drop 5))).fill
        (vals [.i32 c, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 c, .i32 0] (expression (probeBody.drop 5))
      (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) (hfs _ rfl).2.1))
  have hd₂ : decompose? cf.store ((bodyCtx F (expression (probeBody.drop 5))).fill
      (vals [.i32 c, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F (expression (probeBody.drop 5)), 1, 1, [.i32 c, .i32 0]) :=
    decompose_fill _ trivial (hfs _ rfl).2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  -- the host writes the page
  obtain ⟨B₁, hib₁, hW₁⟩ := written_of w hsize
  let mi₁ : MemInst := { mi with bytes := B₁ }
  let s₁ := cf.store.setMem 0 mi₁
  have hs₁ : itemsStore w w cf.store = s₁ := by
    simp only [itemsStore, hmi, hib₁, Option.bind_some, Option.map_some, Option.getD_some, s₁,
      mi₁]
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₁, .values []⟩) (q' := ())
    (by show _ = _; rw [← hs₁]; rfl)
  -- accept(h)
  have hs₁f := hfs s₁ hf₁
  have st₄ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (probeBody.drop 5))).fill
      (Result.values []).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (probeBody.drop 6))]]⟩ :=
    step_body (step_mid [] (expression (probeBody.drop 6)) (step_localGet hv))
  have st₅ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (probeBody.drop 6))]]⟩
      ⟨s₁, {}, (bodyCtx F []).fill (vals [.i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 h] [] (step_call (x := ⟨2⟩) (by rw [hFf]; rfl) hs₁f.2.2.1))
  have hd₃ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 h] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F [], 2, 2, [.i32 h]) :=
    decompose_fill _ trivial hs₁f.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₆ := TSession.call (TSession.of_core_steps t₅ (st₄.steps.trans st₅.steps)) hd₃
  -- the decoded events
  have hco₁ : calloutAt? (probeMod d.ix) (some 0) ⟨cf.store, {},
      (bodyCtx F (expression (probeBody.drop 3))).fill
        (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨d.ix.next.1, d.ix.next.2, .func ⟨0⟩⟩ (some 0) cf.store
        [.i32 h, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? (probeMod d.ix) (some 0) ⟨cf.store, {},
      (bodyCtx F (expression (probeBody.drop 5))).fill
        (vals [.i32 c, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨d.ix.leaf.1, d.ix.leaf.2, .func ⟨1⟩⟩ (some 0) cf.store
        [.i32 c, .i32 0]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? (probeMod d.ix) (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (calloutIn ⟨d.ix.accept.1, d.ix.accept.2, .func ⟨2⟩⟩ (some 0) s₁ [.i32 h]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hrd₁ : probeRead d (calloutIn ⟨d.ix.next.1, d.ix.next.2, .func ⟨0⟩⟩ (some 0) cf.store
      [.i32 h, .i32 0]) ⟨.values [.i32 c], memOf (some 0) cf.store⟩ =
      some (.read (d.q₂ h 0) (d.a₂ c)) := by
    simp [probeRead, calloutIn, Val.i32]
  have hrd₂ : probeRead d (calloutIn ⟨d.ix.leaf.1, d.ix.leaf.2, .func ⟨1⟩⟩ (some 0) cf.store
      [.i32 c, .i32 0]) ⟨.values [], memOf (some 0) s₁⟩ = some (.read (d.q₃ c) a) := by
    have hm : memOf (some 0) s₁ = some B₁ := memOf_setMem hml
    simp [probeRead, calloutIn, Val.i32, hm, hne]
    exact hA _ _ hsize hib₁
  have hna : ∀ (i : Import) (s : Store Nat) (x y : Val),
      probeAccept (Q := Qy) (A := An) d.ix (calloutIn i (some 0) s [x, y]) = none := by
    intro i s x y
    unfold probeAccept
    split
    · simp [calloutIn, Callout.args1]
    · rfl
  have hac : probeAccept (Q := Qy) (A := An) d.ix
      (calloutIn ⟨d.ix.accept.1, d.ix.accept.2, .func ⟨2⟩⟩ (some 0) s₁ [.i32 h]) =
      some (.accept h) := by
    simp [probeAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃] at t₆
  refine ⟨_, ⟨mt, Is, cf, hI, L, (), probeEnv_reply c w _, .run, true, _,
    by rw [hmem0]; exact t₆⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, probeRoles]
  rw [hna, hrd₁, hna, hrd₂, hac]
  rfl

/-- The answers of a valid query are its correct answers. -/
theorem answers_valid {Rd : Reader Qy An (BitVec 32) Y} {ρ : Env (BitVec 32) Y} {q : Qy}
    (hv : Rd.valid ρ q) : answers Rd .trap ρ q = some {a | Rd.ok ρ q a} := by
  unfold answers
  simp [hv]

/-- **The probe accepts `t`** when a fixed environment of `Rhos` makes both reads of the
session valid and correct and names `t` by `h`. -/
theorem probe_live_of (P : Profile) (oa : OnInvalid) {Rd : Reader Qy An (BitVec 32) Y}
    {d : ProbeDec Qy An} (hok : probeOk d.ix = true) (hlive : probeLiveOk d.ix = true)
    {Rhos : Set (Env (BitVec 32) Y)} {ρ : Env (BitVec 32) Y} (hρ : ρ ∈ Rhos) {h c w : BitVec 32}
    {a : An} (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      d.a₃ ⟨.values [], some B'⟩ 0 = a)
    (h₂ : Rd.valid ρ (d.q₂ h 0) ∧ Rd.ok ρ (d.q₂ h 0) (d.a₂ c))
    (h₃ : Rd.valid ρ (d.q₃ c) ∧ Rd.ok ρ (d.q₃ c) a) {t : Y} (ht : ρ h = some t) :
    t ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod d.ix) Rd d .trap oa Rhos := by
  simp only [probeLang, readerLang, langOver, Host.lang]
  refine Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion (probe_traces P hok hlive h c w hA)
    ⟨_, _, .cons .enter
    (.cons (.read (answers_valid h₂.1) h₂.2) (.cons (.read (answers_valid h₃.1) h₃.2)
    (.cons (.acceptOk ht) (.nil _)))), by simp⟩⟩

/-! ## Payloads on the written page -/

/-- The `u64` read at `0` on the page the host wrote. -/
def u64Page : BitVec 64 := 8 + 2 * 2 ^ 32

theorem bytesPay_page (dec : List UInt8 → Option α) (b₀ b₁ : UInt8) {B B' : ByteArray}
    (hB : B.size = 65536) (hw : itemsBytes (symWord b₀ b₁) (symWord b₀ b₁) B = some B') :
    bytesPay dec ⟨.values [], some B'⟩ 0 = dec [b₀, b₁] := by
  obtain ⟨B'', hib, hW⟩ := written_of (symWord b₀ b₁) hB
  rw [hw] at hib
  cases hib
  simp [bytesPay, written_bytesList hW]

theorem u64Pay_page (w : BitVec 32) {B B' : ByteArray} (hB : B.size = 65536)
    (hw : itemsBytes w w B = some B') : u64Pay ⟨.values [], some B'⟩ 0 = some u64Page := by
  obtain ⟨B'', hib, hW⟩ := written_of w hB
  rw [hw] at hib
  cases hib
  obtain ⟨hz, h8, h2b, -, -⟩ := hW
  have e₀ : segOf B' 0 8 = some ((Memory.encodeLE 4 (8 : BitVec 32).toNat).data.toList ++
      (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList) := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide),
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, h8, h2b]
  simp only [u64Pay, Option.bind_some]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, e₀]
  decide +kernel

/-- The word at `[8, 12)` of the written page is `w`. -/
theorem written_word8 {w : BitVec 32} {B : ByteArray} (hW : Written w B) :
    (segOf B (0 + 8) 4).bind le32s = some [w] := by
  obtain ⟨hz, -, -, hh₁, -⟩ := hW
  have e : segOf B (0 + 8) 4 = some (Memory.encodeLE 4 w.toNat).data.toList := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide), hh₁]
  rw [e, Option.bind_some, ← List.append_nil (Memory.encodeLE 4 w.toNat).data.toList,
    le32s_encode]
  rfl

theorem kindPay_page (dec : BitVec 32 → List UInt8 → Option α) (k : UInt8) {B B' : ByteArray}
    (hB : B.size = 65536) (hw : itemsBytes (symWord k 0) (symWord k 0) B = some B') :
    kindPay dec ⟨.values [], some B'⟩ 0 = dec (symWord k 0) [k, 0] := by
  obtain ⟨B'', hib, hW⟩ := written_of (symWord k 0) hB
  rw [hw] at hib
  cases hib
  simp only [kindPay, Option.bind_some, show (0 : BitVec 32).toNat = 0 from rfl,
    written_bytesList hW, written_word8 hW]

/-- The hinted atom on the page written with `w = 4`: the octets `4 0`, the hint `2 0 0 0`. -/
theorem hintPay_page {B B' : ByteArray} (hB : B.size = 65536)
    (hw : itemsBytes 4 4 B = some B') :
    hintPay ⟨.values [], some B'⟩ 0 = some (some [2, 0, 0, 0], [4, 0]) := by
  obtain ⟨B'', hib, hW⟩ := written_of 4 hB
  rw [hw] at hib
  cases hib
  have hW' : Written (symWord 4 0) B' := hW
  obtain ⟨hz, -, h2b, hh₁, hh₂⟩ := hW
  have e₈ : segOf B' 8 8 = some ((Memory.encodeLE 4 (4 : BitVec 32).toNat).data.toList ++
      (Memory.encodeLE 4 (4 : BitVec 32).toNat).data.toList) := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide),
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, hh₁, hh₂]
  have e₄ : segOf B' 4 4 = some (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide), h2b]
  have hl : bytesList B' (0 + 8) = some [2, 0, 0, 0] := by
    unfold bytesList
    rw [show (0 + 8 : Nat) = 8 from rfl, e₈]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [le32s_encode, ← List.append_nil (Memory.encodeLE 4 (4 : BitVec 32).toNat).data.toList,
      le32s_encode]
    simp only [le32s, Option.map_some, Option.bind_some, pair32]
    rw [show (4 : BitVec 32).toNat = 4 from rfl, e₄]
    rfl
  simp only [hintPay, Option.bind_some, show (0 : BitVec 32).toNat = 0 from rfl,
    written_bytesList hW', written_word8 hW', hl]
  decide

/-! ## The three probes -/

theorem naryOk : probeOk naryIx = true := by decide +kernel
theorem consOk : probeOk consIx = true := by decide +kernel
theorem astOk : probeOk astIx = true := by decide +kernel
theorem naryLiveOk : probeLiveOk naryIx = true := by decide +kernel
theorem consLiveOk : probeLiveOk consIx = true := by decide +kernel
theorem astLiveOk : probeLiveOk astIx = true := by decide +kernel

/-- The environment naming `t` by `1` and `x` by `2`. -/
def env2 (t x : Y) : Env (BitVec 32) Y := fun k => if k = 1 then some t else if k = 2 then some x
  else none

theorem env2_one (t x : Y) : env2 t x 1 = some t := rfl

theorem env2_two (t x : Y) : env2 t x 2 = some x := by
  simp [env2]

theorem nary_sound (P : Profile) (pay : Payload α) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) (SExp α))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx) (sexpR α (BitVec 32))
      (naryProbe pay) .trap oa Rhos ⊆ firstAtoms α :=
  probe_sound P naryOk (nary_facts pay) hoa Rhos

theorem cons_sound (P : Profile) (pay : Payload α) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) (SExp2 α))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx) (consR α (BitVec 32))
      (consProbe pay) .trap oa Rhos ⊆ carAtoms α :=
  probe_sound P consOk (cons_facts pay) hoa Rhos

theorem ast_sound (P : Profile) (pay : Payload α) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) (AST (sexpSig α)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx) (astR (sexpSig α) (BitVec 32))
      (astProbe pay) .trap oa Rhos ⊆ firstLeaves α :=
  probe_sound P astOk (ast_facts pay) hoa Rhos

theorem nary_live (P : Profile) (oa : OnInvalid) (pay : Payload α) (w : BitVec 32) {x : α}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      pay ⟨.values [], some B'⟩ 0 = some x) :
    SExp.ofList [.atom x] ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR α (BitVec 32)) (naryProbe pay) .trap oa Set.univ :=
  probe_live_of (Rd := sexpR α (BitVec 32)) (d := naryProbe pay) P oa naryOk naryLiveOk
    (Set.mem_univ (env2 (SExp.ofList [.atom x]) (.atom x))) (h := 1) (c := 2) (w := w)
    (a := .atom x) (fun B B' hB hw => by simp only [naryProbe, hA B B' hB hw])
    ⟨⟨[.atom x], env2_one _ _, by simp⟩, ⟨[.atom x], .atom x, env2_one _ _, rfl, env2_two _ _⟩⟩
    ⟨⟨x, env2_two _ _⟩, env2_two _ _⟩ (env2_one _ _)

theorem cons_live (P : Profile) (oa : OnInvalid) (pay : Payload α) (w : BitVec 32) {x : α}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      pay ⟨.values [], some B'⟩ 0 = some x) :
    SExp2.cons (.atom x) .nil ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR α (BitVec 32)) (consProbe pay) .trap oa Set.univ :=
  probe_live_of (Rd := consR α (BitVec 32)) (d := consProbe pay) P oa consOk consLiveOk
    (Set.mem_univ (env2 (SExp2.cons (.atom x) .nil) (.atom x))) (h := 1) (c := 2) (w := w)
    (a := .atom x) (fun B B' hB hw => by simp only [consProbe, hA B B' hB hw])
    ⟨⟨.atom x, .nil, env2_one _ _⟩, ⟨.atom x, .nil, env2_one _ _, env2_two _ _⟩⟩
    ⟨⟨x, env2_two _ _⟩, env2_two _ _⟩ (env2_one _ _)

/-- The node with one leaf child `x`. -/
abbrev leafNode (x : α) : AST (sexpSig α) :=
  AST.node (S := sexpSig α) SxTag.branch () [AST.node (S := sexpSig α) SxTag.leaf x []]

theorem ast_live (P : Profile) (oa : OnInvalid) (pay : Payload α) (w : BitVec 32) {x : α}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      pay ⟨.values [], some B'⟩ 0 = some x) :
    leafNode x ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx)
      (astR (sexpSig α) (BitVec 32)) (astProbe pay) .trap oa Set.univ :=
  probe_live_of (Rd := astR (sexpSig α) (BitVec 32)) (d := astProbe pay) P oa astOk astLiveOk
    (Set.mem_univ (env2 (leafNode x) (AST.node (S := sexpSig α) SxTag.leaf x [])))
    (h := 1) (c := 2) (w := w) (a := .tag ⟨SxTag.leaf, x⟩)
    (fun B B' hB hw => by simp only [astProbe, hA B B' hB hw])
    ⟨⟨_, [AST.node (S := sexpSig α) SxTag.leaf x []], env2_one _ _, by simp⟩,
      ⟨_, [AST.node (S := sexpSig α) SxTag.leaf x []], _, env2_one _ _, rfl, env2_two _ _⟩⟩
    ⟨⟨_, env2_two _ _⟩, ⟨[], env2_two _ _⟩⟩ (env2_one _ _)

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe
