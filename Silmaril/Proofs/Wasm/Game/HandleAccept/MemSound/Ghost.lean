module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Bridge
public import Silmaril.Wasm.SingleThreaded.Agreement

/-!
# Proofs: the ghost bridge between the program logic and traced sessions

The real configurations of a traced session (`TSession`, `Config Nat`) are related to the
configurations of the specification world `gConfig g c` (`Config (Nat × G)`: every host function
carries the ghost `g`, nothing else changes):

* a host-free step of `c` is a host-free step of `gConfig g c` (`Step.mapH`), with the same ghost;
* a host-call redex of `c` is one of `gConfig g c` with host code `(h, g)` (`gDecompose`, from
  `decompose?_sound` and the completeness of `decompose?`); the ghost of the call is read back
  from the store (`gStore_inj`: a store with a host function determines its ghost);
* an answer `a` of the real environment meeting the contract's reply condition and answer
  assumption is a step of `gHost` to `gConfig g' c'`, `g'` the ghost moved over the inputs the
  call and the answer decode to (`gstep_answer`);
* an invocation of the real store is the invocation of the relabelled store (`invoke_mapH`).

`tsession_ggood`: along a traced session, the relabelled configuration, with the ghost of the
decoded prefix (`tagGhost`), is safe under `gHost` as long as every decoded answer met `K.ans`;
while a call is tagged and not yet answered, the configuration is at that call's redex and the
ghost is the one before the call's tags. Every input decoded at a call meets `K.pre` in the ghost
of the inputs before it; every input decoded at an answer comes from a callout meeting `K.pre` in
some ghost (`PreOkG`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (AllIn AllIn.left AllIn.right split_append)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH Config.mapH FuncInst.mapH FuncCode.mapH
  Step.mapH invoke_mapH)

variable {X I O C G : Type}

/-! ## Ghost-carrying stores -/

theorem gStore_funcs (g : G) (s : Store Nat) (a : Nat) :
    (gStore g s).funcs[a]? = (s.funcs[a]?).map (FuncInst.mapH (ghostH g)) := by
  simp [gStore, Store.mapH]

theorem gStore_mems (g : G) (s : Store Nat) : (gStore g s).mems = s.mems := rfl

theorem funcInst_ghost_inj (g : G) : Function.Injective (FuncInst.mapH (ghostH g)) := by
  rintro ⟨t, m, c⟩ ⟨t', m', c'⟩ h
  simp only [FuncInst.mapH, FuncInst.mk.injEq] at h
  obtain ⟨rfl, rfl, hc⟩ := h
  cases c <;> cases c' <;> simp_all [FuncCode.mapH, ghostH]

/-- **A store with a host function determines its ghost.** -/
theorem gStore_inj {g g' : G} {s s' : Store Nat} (h : gStore g s = gStore g' s') {a k : Nat}
    {fi : FuncInst Nat} (hf : s.funcs[a]? = some fi) (hc : fi.code = .host k) :
    g = g' ∧ s = s' := by
  have hfa : (gStore g s).funcs[a]? = (gStore g' s').funcs[a]? := by rw [h]
  rw [gStore_funcs, gStore_funcs, hf] at hfa
  rcases hf' : s'.funcs[a]? with _ | fi'
  · rw [hf'] at hfa; cases hfa
  rw [hf'] at hfa
  simp only [Option.map_some, Option.some.injEq] at hfa
  have hcode := congrArg FuncInst.code hfa
  have hgg : g = g' := by
    cases hc' : fi'.code with
    | wasm f => simp [FuncInst.mapH, hc, hc', FuncCode.mapH] at hcode
    | host k' =>
      simp only [FuncInst.mapH, hc, hc', FuncCode.mapH, ghostH, FuncCode.host.injEq,
        Prod.mk.injEq] at hcode
      exact hcode.2
  subst hgg
  refine ⟨rfl, ?_⟩
  rcases s with ⟨t1, g1, m1, tb1, f1, d1, e1, st1, a1, x1⟩
  rcases s' with ⟨t2, g2, m2, tb2, f2, d2, e2, st2, a2, x2⟩
  simp only [gStore, Store.mapH, Store.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, hfs, rfl, rfl, rfl, rfl, rfl⟩ := h
  obtain rfl := (List.map_injective_iff.2 (funcInst_ghost_inj g)) hfs
  rfl

/-- **Erasing the ghost gives the real store back.** -/
theorem gStore_erase (g : G) (s : Store Nat) : Store.mapH Prod.fst (gStore g s) = s := by
  rcases s with ⟨t1, g1, m1, tb1, f1, d1, e1, st1, a1, x1⟩
  simp only [gStore, Store.mapH, List.map_map, Store.mk.injEq, true_and, and_true]
  conv_rhs => rw [← List.map_id f1]
  refine List.map_congr_left fun ⟨t, m, c⟩ _ => ?_
  cases c <;> rfl

/-- **Erasing the ghost gives the real configuration back.** -/
theorem gConfig_erase (g : G) (c : Config Nat) : Config.mapH Prod.fst (gConfig g c) = c := by
  rcases c with ⟨s, f, code⟩
  show (⟨Store.mapH Prod.fst (gStore g s), f, code⟩ : Config Nat) = ⟨s, f, code⟩
  rw [gStore_erase]

/-! ## Redexes -/

/-- Completeness of `decompose?` at any host type. -/
theorem decompose_fill' {H : Type} {s : Store H} (E : SingleThreaded.Ctx) {args : List Val}
    {a : Nat} {c : Admin} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : args.length = ps.length) (hcode : fi.code = .host h) :
    decompose? s (E.fill (vals args ++ [.ref (.func a), c])) = some (E, a, h, args) := by
  open Silmaril.Wasm.SingleThreaded in
  induction E with
  | top pre rest =>
    have := decompose?_wrap pre rest (decompose?_redex hc hf he hn hcode)
    simpa [Ctx.wrap, Ctx.fill] using this
  | label pre n cont E rest ih =>
    have hsp : splitVals (Ctx.fill (.label pre n cont E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .label n cont (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]
  | handler pre n cs E rest ih =>
    have hsp : splitVals (Ctx.fill (.handler pre n cs E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .handler n cs (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]
  | frame pre n f E rest ih =>
    have hsp : splitVals (Ctx.fill (.frame pre n f E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .frame n f (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]

/-- **A real redex is a redex of the relabelled configuration**, with host code `(h, g)`. -/
theorem gDecompose {g : G} {s : Store Nat} {code : List Admin} {E : SingleThreaded.Ctx}
    {fa h : Nat} {args : List Val} (hd : decompose? s code = some (E, fa, h, args)) :
    decompose? (gStore g s) code = some (E, fa, (h, g), args) := by
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ :=
    Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hcode]
  exact decompose_fill' E hyy (fi := FuncInst.mapH (ghostH g) fi) (by rw [gStore_funcs, hf]; rfl)
    he hn (by simp [FuncInst.mapH, hc, FuncCode.mapH, ghostH])

/-- A redex is not a finished run. -/
theorem decompose_none_of_finished {b : Bool} {c : Config Nat} (fin : Finished b c) :
    decompose? c.store c.code = none := by
  rcases hd : decompose? c.store c.code with _ | ⟨E, fa, h, args⟩
  · rfl
  exfalso
  have hex : ∃ o, Exits o c.code := by
    cases b with
    | false => obtain ⟨vs, hc⟩ := fin; exact ⟨.normal vs, hc⟩
    | true =>
      obtain ⟨r, hc⟩ := fin
      rcases r with vs | a | _
      · exact ⟨.normal vs, hc⟩
      · exact ⟨.throw a, [], [], by simpa [Result.toAdmin, throwing] using hc⟩
      · exact ⟨.trap, [], [], by simpa [Result.toAdmin] using hc⟩
  obtain ⟨o, ho⟩ := hex
  exact Silmaril.Wasm.Logic.Open.not_exits_of_redex (P := Numerics.Profile.spec false {}) hd o ho

section Steps

variable {P : Numerics.Profile} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {K : GContract I G} {Inv : G → Store Nat → Prop}

/-- **The precondition at a real call redex**, read from a safe relabelled configuration. -/
theorem gpre_of_safe {Q : Post (Nat × G)} {g : G} {c : Config Nat} {E : SingleThreaded.Ctx}
    {fa h : Nat} {args : List Val} (hs : ∀ n, Safe P (gHost m memAddr R K) Q n (gConfig g c))
    (hd : decompose? c.store c.code = some (E, fa, h, args)) :
    ∃ i, m.imports[h]? = some i ∧
      calloutAt? m memAddr c = some (calloutIn i memAddr c.store args) ∧
      K.pre g (calloutIn i memAddr c.store args) := by
  obtain ⟨S, hS, hpre⟩ := Silmaril.Wasm.Logic.Open.import_pre (hs 1)
    (show decompose? (gConfig g c).store (gConfig g c).code = _ from gDecompose (g := g) hd)
  simp only [gCtx, Option.map_eq_some_iff] at hS
  obtain ⟨i, hi, rfl⟩ := hS
  obtain ⟨g', sR, hgs, hp⟩ := hpre
  obtain ⟨fi, yy, ps, rs, hf, hc, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  obtain ⟨rfl, rfl⟩ := gStore_inj hgs hf hc
  refine ⟨i, hi, ?_, hp⟩
  unfold calloutAt?
  rw [hd]
  simp [hi, calloutIn]

/-- **An admitted answer is a step of `gHost`**, to the relabelled answer configuration with the
moved ghost. -/
theorem gstep_answer {g : G} {c : Config Nat} {E : SingleThreaded.Ctx} {fa h : Nat}
    {args : List Val} {i : Import} {a : UReply}
    (hd : decompose? c.store c.code = some (E, fa, h, args)) (hi : m.imports[h]? = some i)
    (hpre : K.pre g (calloutIn i memAddr c.store args)) (hrep : K.reply ⟨h, c.store, args⟩ a)
    (hans : ∀ x, R.answerIn (calloutIn i memAddr c.store args)
      ⟨a.result, memOf memAddr a.store⟩ = some x → K.ans x) :
    Step P (gHost m memAddr R K) (gConfig g c)
      (gConfig (ansGhost R K g (calloutIn i memAddr c.store args)
        ⟨a.result, memOf memAddr a.store⟩) ⟨a.store, c.frame, E.fill a.result.toAdmin⟩) :=
  Silmaril.Wasm.Logic.Open.redex_step_ret
    (show decompose? (gConfig g c).store (gConfig g c).code = _ from gDecompose (g := g) hd)
    ⟨gImportSpec h i memAddr R K, by simp [gCtx, hi], ⟨g, c.store, rfl, hpre⟩,
      ⟨g, c.store, rfl, a.result, a.store, rfl, rfl, hrep, hans⟩⟩

end Steps

/-! ## Ghosts of tag lists -/

theorem tagGhost_append (upd : G → I → G) (g : G) (ts us : List (Tag X I O C)) :
    tagGhost upd g (ts ++ us) = tagGhost upd (tagGhost upd g ts) us := by
  induction ts generalizing g with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [tagGhost, ih]

theorem tagGhost_callTags (R : Roles X I O C) (K : GContract I G) (g : G) (o : Callout) :
    tagGhost K.upd g (R.callTags o) = callGhost R K g o := by
  simp only [Roles.callTags, callGhost, GContract.after]
  rcases R.callIn o with _ | y <;> rcases R.callOut o with _ | z <;> rfl

theorem tagGhost_answerTags (R : Roles X I O C) (K : GContract I G) (g : G) (o : Callout)
    (w : HostReply) : tagGhost K.upd g (R.answerTags o w) = K.after g (R.answerIn o w) := by
  simp only [Roles.answerTags, GContract.after]
  rcases R.answerIn o w with _ | y <;> rfl

theorem callTags_split {R : Roles X I O C} {o : Callout} {u v : List (Tag X I O C)} {x : I}
    (h : R.callTags o = u ++ .inp x :: v) : u = [] ∧ R.callIn o = some x := by
  unfold Roles.callTags at h
  rcases hc : R.callIn o with _ | y <;> rcases ho : R.callOut o with _ | z <;>
    simp only [hc, ho, Option.toList_none, Option.toList_some, List.map_nil, List.map_cons,
      List.nil_append, List.append_nil, List.cons_append] at h <;>
    rcases u with _ | ⟨t, _ | ⟨t', u⟩⟩ <;> simp_all

theorem answerTags_split {R : Roles X I O C} {o : Callout} {w : HostReply}
    {u v : List (Tag X I O C)} {x : I} (h : R.answerTags o w = u ++ .inp x :: v) :
    u = [] ∧ R.answerIn o w = some x := by
  unfold Roles.answerTags at h
  rcases hc : R.answerIn o w with _ | y <;>
    simp only [hc, Option.toList_none, Option.toList_some, List.map_nil, List.map_cons] at h <;>
    rcases u with _ | ⟨t, _ | ⟨t', u⟩⟩ <;> simp_all

theorem no_inp_single {t : Tag X I O C} (ht : ∀ y, t ≠ .inp y) {u v : List (Tag X I O C)} {x : I}
    (h : [t] = u ++ .inp x :: v) : False := by
  rcases u with _ | ⟨a, u⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    exact ht x h.1
  · simp at h

/-! ## The session invariant -/

/-- Every input of a tag list preceded by inputs meeting `K.ans` is decoded at a call meeting
`K.pre` in the ghost of the inputs before it, or at the answer of a call meeting `K.pre`. -/
def PreOkG (R : Roles X I O C) (K : GContract I G) (g₀ : G) (ts : List (Tag X I O C)) : Prop :=
  ∀ u x v, ts = u ++ .inp x :: v → AllIn K.ans u →
    ∃ o, (R.callIn o = some x ∧ K.pre (tagGhost K.upd g₀ u) o) ∨
      (∃ w, R.answerIn o w = some x ∧ ∃ g, K.pre g o)

theorem PreOkG.append {R : Roles X I O C} {K : GContract I G} {g₀ : G}
    {ts N : List (Tag X I O C)} (h : PreOkG R K g₀ ts)
    (hN : ∀ u' x v, N = u' ++ .inp x :: v → AllIn K.ans (ts ++ u') →
      ∃ o, (R.callIn o = some x ∧ K.pre (tagGhost K.upd g₀ (ts ++ u')) o) ∨
        (∃ w, R.answerIn o w = some x ∧ ∃ g, K.pre g o)) :
    PreOkG R K g₀ (ts ++ N) := by
  intro u x v he hu
  rcases split_append he with ⟨v', hv'⟩ | ⟨u', rfl, hN'⟩
  · exact h u x v' hv' hu
  · exact hN u' x v hN' hu

/-- The safety of a relabelled configuration in a phase. -/
def GGood (P : Numerics.Profile) (m : Module) (memAddr : Option Nat) (R : Roles X I O C)
    (K : GContract I G) (Inv : G → Store Nat → Prop) :
    IOAccept.Phase → Config (Nat × G) → Prop
  | .inst, c => ∀ n, Safe P (gHost m memAddr R K) (gInstPost Inv) n c
  | _, c => ∀ n, Safe P (gHost m memAddr R K)
      (callPost {} [] fun s _ => ∀ g sR, s = gStore g sR → Inv g sR) n c

/-- **The session invariant**: outside a tagged call, the relabelled configuration with the ghost
of the tags is good; at a tagged call, the configuration is at the call's redex and good with
the ghost before the call's tags. -/
def TInv (P : Numerics.Profile) (m : Module) (memAddr : Option Nat) (R : Roles X I O C)
    (K : GContract I G) (Inv : G → Store Nat → Prop) (g₀ : G) :
    IOAccept.Phase → Bool → Config Nat → List (Tag X I O C) → Prop
  | p, false, c, ts =>
      AllIn K.ans ts → GGood P m memAddr R K Inv p (gConfig (tagGhost K.upd g₀ ts) c)
  | p, true, c, ts => ∃ (ts₀ : List (Tag X I O C)) (E : SingleThreaded.Ctx) (fa h : Nat)
      (args : List Val),
      decompose? c.store c.code = some (E, fa, h, args) ∧
      ts = ts₀ ++ (calloutAt? m memAddr c).elim [] R.callTags ∧
      (AllIn K.ans ts₀ → GGood P m memAddr R K Inv p (gConfig (tagGhost K.upd g₀ ts₀) c))

section Session

variable {P : Numerics.Profile} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {K : GContract I G} {Inv : G → Store Nat → Prop}

theorem ggood_pre {p : IOAccept.Phase} {g : G} {c : Config Nat} {E : SingleThreaded.Ctx}
    {fa h : Nat} {args : List Val} (hg : GGood P m memAddr R K Inv p (gConfig g c))
    (hd : decompose? c.store c.code = some (E, fa, h, args)) :
    ∃ i, m.imports[h]? = some i ∧
      calloutAt? m memAddr c = some (calloutIn i memAddr c.store args) ∧
      K.pre g (calloutIn i memAddr c.store args) := by
  cases p
  · exact gpre_of_safe hg hd
  · exact gpre_of_safe hg hd
  · exact gpre_of_safe hg hd

theorem ggood_step {p : IOAccept.Phase} {c c' : Config (Nat × G)}
    (hg : GGood P m memAddr R K Inv p c) (st : Step P (gHost m memAddr R K) c c') :
    GGood P m memAddr R K Inv p c' := by
  cases p <;> exact fun n => (hg (n + 1)).step_inv st

/-- The ghost invariant at the end of a finished run. -/
theorem ginv_of_finished {p : IOAccept.Phase} {g : G} {c : Config Nat} (hp : p ≠ .run)
    (hg : GGood P m memAddr R K Inv p (gConfig g c)) (fin : Finished p.started c) :
    Inv g c.store := by
  cases p with
  | run => exact absurd rfl hp
  | inst =>
    obtain ⟨vs, hc⟩ := fin
    have hc' : gConfig g c = ⟨gStore g c.store, c.frame, vals vs⟩ := by
      rcases c with ⟨s, f, code⟩
      simp only at hc
      simp [gConfig, Config.mapH, gStore, hc, Result.toAdmin]
    have hsafe := hg 1
    rw [hc'] at hsafe
    obtain ⟨o, he, hq⟩ := hsafe.exit_of_stuck fun _ => not_step_vals
    exact hq vs (exits_vals_inv he) g c.store rfl
  | idle =>
    obtain ⟨r, hc⟩ := fin
    have hc' : gConfig g c = ⟨gStore g c.store, c.frame, r.toAdmin⟩ := by
      rcases c with ⟨s, f, code⟩
      simp only at hc
      simp [gConfig, Config.mapH, gStore, hc]
    have hsafe := hg 1
    rw [hc'] at hsafe
    exact Silmaril.Wasm.Logic.Open.final_post
      (R := fun s _ => ∀ g sR, s = gStore g sR → Inv g sR) hsafe g c.store rfl

/-- **The session invariant of the ghost bridge.** -/
theorem tsession_ggood {L : SEnv UImp} {g₀ : G} {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    (hinst : ∀ n, Safe P (gHost m memAddr R K) (gInstPost Inv) n (gConfig g₀ c₀))
    (hexp : ∀ a ∈ addrs, FSpecValid P (gHost m memAddr R K) a (gExportSpec Inv a))
    (hL : ∀ q e a q', L.Ans q e a q' → K.reply e a)
    {p : IOAccept.Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    TInv P m memAddr R K Inv g₀ p w x.1 ts ∧ PreOkG R K g₀ ts := by
  induction h with
  | start => exact ⟨fun _ => hinst, fun u x v he => by simp at he⟩
  | @internal p w c c' _ ts _ st ih =>
    refine ⟨?_, ih.2⟩
    cases w with
    | false =>
      intro hA
      have st' := Step.of_noHost (gHost m memAddr R K)
        (Step.mapH (ghostH (tagGhost K.upd g₀ ts)) st)
      exact ggood_step (ih.1 hA) st'
    | true =>
      obtain ⟨_, _, _, _, _, hd, -⟩ := ih.1
      exact absurd ((Silmaril.Wasm.Logic.Open.decompose?_none_of_step st).symm.trans hd)
        (by simp)
  | @call p c _ ts E fa h args _ hd ih =>
    refine ⟨⟨ts, E, fa, h, args, hd, rfl, ih.1⟩, ih.2.append fun u' x v hN hA => ?_⟩
    obtain ⟨i, -, ho, hpre⟩ := ggood_pre (ih.1 (AllIn.left hA)) hd
    rw [ho] at hN
    obtain ⟨rfl, hx⟩ := callTags_split hN
    exact ⟨_, .inl ⟨hx, by simpa using hpre⟩⟩
  | @answer p c _ _ ts E fa h args a _ hd ans ih =>
    obtain ⟨ts₀, E', fa', h', args', hd', hts, hG⟩ := ih.1
    rw [hd] at hd'
    obtain ⟨rfl, rfl, rfl, rfl⟩ : E = E' ∧ fa = fa' ∧ h = h' ∧ args = args' := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'; exact hd'
    refine ⟨fun hA => ?_, ih.2.append fun u' x v hN hA => ?_⟩
    · have hA₀ : AllIn K.ans ts₀ := AllIn.left (ts := ts₀) (by rw [← hts]; exact AllIn.left hA)
      have hg := hG hA₀
      obtain ⟨i, hi, ho, hpre⟩ := ggood_pre hg hd
      have ho' : calloutAt? m memAddr c = some (calloutIn i memAddr c.store args) := ho
      rw [ho'] at hts hA ⊢
      simp only [Option.elim] at hts hA ⊢
      have hst := gstep_answer (P := P) (R := R) (K := K) hd hi hpre (hL _ _ _ _ ans)
        (fun x hx => AllIn.right hA x (by simp [Roles.answerTags, hx]))
      have hgh : tagGhost K.upd g₀ (ts ++ R.answerTags (calloutIn i memAddr c.store args)
          ⟨a.result, memOf memAddr a.store⟩) =
          ansGhost R K (tagGhost K.upd g₀ ts₀) (calloutIn i memAddr c.store args)
            ⟨a.result, memOf memAddr a.store⟩ := by
        rw [hts, tagGhost_append, tagGhost_append, tagGhost_callTags, tagGhost_answerTags]
        rfl
      rw [hgh]
      exact ggood_step hg hst
    · have hA₀ : AllIn K.ans ts₀ := AllIn.left (ts := ts₀) (by rw [← hts]; exact AllIn.left hA)
      obtain ⟨i, -, ho, hpre⟩ := ggood_pre (hG hA₀) hd
      rw [ho] at hN
      obtain ⟨rfl, hx⟩ := answerTags_split hN
      exact ⟨_, .inr ⟨_, hx, _, hpre⟩⟩
  | @invoke p w c _ ts a args _ hp fin ha ok ih =>
    refine ⟨fun hA => ?_, ih.2.append fun u' x v hN _ => (no_inp_single (by simp) hN).elim⟩
    cases w with
    | true =>
      obtain ⟨_, _, _, _, _, hd, -⟩ := ih.1
      exact absurd ((decompose_none_of_finished fin).symm.trans hd) (by simp)
    | false =>
      have hinv := ginv_of_finished hp (ih.1 (AllIn.left hA)) fin
      rw [tagGhost_append]
      simp only [tagGhost]
      intro n
      have := hexp a ha n (gStore (tagGhost K.upd g₀ ts) c.store) args
        ⟨_, c.store, rfl, hinv, ok⟩ {} []
        (.callRefType (((gStore (tagGhost K.upd g₀ ts) c.store).funcs[a]?.map
          FuncInst.type).getD default))
        (show Admin.IsCallRef (.callRefType _) from trivial)
      rw [gConfig, invoke_mapH]
      simpa [invoke, gExportSpec, gStore] using this
  | @ret w c _ ts r _ hr ih =>
    refine ⟨fun hA => ?_, ih.2.append fun u' x v hN _ => (no_inp_single (by simp) hN).elim⟩
    cases w with
    | true =>
      obtain ⟨_, _, _, _, _, hd, -⟩ := ih.1
      exact absurd ((decompose_none_of_finished (b := true) ⟨r, hr⟩).symm.trans hd) (by simp)
    | false =>
      rw [tagGhost_append]
      exact ih.1 (AllIn.left hA)

end Session

/-- **The ghost bridge**: in every traced session of a module meeting `GMemSat` from the ghost
`g₀`, every input preceded by inputs meeting `K.ans` is decoded at a call meeting `K.pre` in the
ghost of the inputs before it, or at the answer of a call meeting `K.pre`. -/
theorem tagTraces_gpre {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {R : Roles X I O C} {K : GContract I G}
    {Inv : G → Store Nat → Prop} {g₀ : G} (hsat : GMemSat P m memIdx R K Inv g₀)
    (hE : ∀ s L, Envs s L → ReplyEnvs K.reply s L) {ts : List (Tag X I O C)}
    (hts : ts ∈ tagTraces P Envs memIdx m R) {u v : List (Tag X I O C)} {x : I}
    (hd : ts = u ++ .inp x :: v) (hu : ∀ y, Tag.inp y ∈ u → K.ans y) :
    ∃ o, (R.callIn o = some x ∧ K.pre (tagGhost K.upd g₀ u) o) ∨
      (∃ w, R.answerIn o w = some x ∧ ∃ g, K.pre g o) := by
  obtain ⟨mt, Is, c₀, hI, L, q₀, hL, p, w, y, ht⟩ := hts
  obtain ⟨hinst, hexp⟩ := hsat mt Is c₀ hI
  exact (tsession_ggood hinst hexp (hE _ _ hL) ht).2 u x v hd hu

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost
