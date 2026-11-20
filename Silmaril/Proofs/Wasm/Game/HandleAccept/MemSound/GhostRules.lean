module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# Proofs: program-logic rules in the ghost specification world

The rules of `Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules`, for stores over host code
`Nat × G`:

* the straight-line rules (`GX.localGet`, `GX.localSet`, `GX.i32Const`, `GX.done`);
* **the import call rule under a ghost contract** (`hwp_gcall`): in the store `gStore g sR`, the
  call of import `k` is allowed when `K.pre g` holds of the callout read in `sR`; every reply the
  contract admits continues in `gStore g' sR'`, `g'` the ghost moved over the inputs the call and
  its answer decode to;
* `gexport_valid`: an export meets `gExportSpec Inv a` if its body is safe from every
  `gStore g sR` with `Inv g sR`, for every postcondition accepting the body's exits in such
  stores.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)
open Silmaril.Proofs.Wasm.Component.Reference (FuncInst.mapH FuncCode.mapH)

variable {G : Type}

/-! ## Straight-line rules -/

section Straight

variable {P : Profile} {host : HostSemantics (Nat × G)} {s : Store (Nat × G)} {f : Frame}
  {us : List Val} {is : List Instr} {Q : Post (Nat × G)}

theorem GX.localGet {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v))
    (h : HWP P host s f (vals (us ++ [v]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.localGet x :: is)) Q :=
  HWP.localGet hv h

theorem GX.localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    (h : HWP P host s (f.setLocal x v) (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [v]) ++ expression (.localSet x :: is)) Q :=
  HWP.localSet hx h

theorem GX.i32Const {c : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.intConst .i32 c :: is)) Q := by
  simpa [vals, expression, Val.i32, Val.toAdmin] using h

/-- The end of the body. -/
theorem GX.done (hq : Q s f (.normal us)) : HWP P host s f (vals us ++ expression []) Q :=
  HWP.of_exits (o := .normal us) (show vals us ++ expression [] = vals us by simp [expression]) hq

end Straight

/-! ## Exits and exports -/

/-- `Q` accepts every exit of a function body without results, in every store `gStore g sR` with
`Inv g sR`. -/
def GBodyExits (Inv : G → Store Nat → Prop) (Q : Post (Nat × G)) : Prop :=
  ∀ g sR, Inv g sR → ∀ f, Q (gStore g sR) f (.normal []) ∧ (∀ vs, Q (gStore g sR) f (.ret vs)) ∧
    Q (gStore g sR) f .trap ∧ ∀ a, Q (gStore g sR) f (.throw a)

/-- **An export meets `gExportSpec`** if its body is safe from every store meeting the ghost
invariant, for every postcondition accepting its exits in such stores. -/
theorem gexport_valid {P : Profile} {host : HostSemantics (Nat × G)}
    {Inv : G → Store Nat → Prop} {a : Nat} {fi : FuncInst Nat} {code : Func}
    {ps rs : Ty (.list .val)} (hfi : ∀ g sR, Inv g sR → sR.funcs[a]? = some fi)
    (hhost : ∀ g sR, Inv g sR → ∃ (a' k : Nat) (fk : FuncInst Nat), sR.funcs[a']? = some fk ∧
      fk.code = .host k)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs)) (hrs : rs.length = 0)
    (hbody : ∀ g sR args, Inv g sR → InvokeOk sR a args → ∀ Q : Post (Nat × G),
      GBodyExits Inv Q →
      HWP P host (gStore g sR) (Frame.forCall fi.module args code.locals)
        (vals [] ++ expression code.body) Q) :
    FSpecValid P host a (gExportSpec Inv a) := by
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    let fiS : FuncInst (Nat × G) := ⟨fi.type, fi.module, .wasm code⟩
    have hfiS : ∀ g sR, Inv g sR → (gStore g sR).funcs[a]? = some fiS := by
      intro g sR h
      rw [gStore_funcs, hfi g sR h]
      simp [fiS, FuncInst.mapH, hcode, FuncCode.mapH]
    refine FSpecAt.of_body (fi := fiS) (fun s args hpre => ?_) rfl he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨g, sR, rfl, hInv, -⟩ := hpre
      exact hfiS g sR hInv
    · obtain ⟨g, sR, rfl, hInv, fi', ps', rs', hf', he', hall⟩ := hpre
      obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans (hfi g sR hInv))
      have hps : ps' = ps := by
        have h1 := Expand.iff.1 he
        have h2 := Expand.iff.1 he'
        rw [h1] at h2
        cases h2
        rfl
      subst hps
      exact hall.length_eq
    · obtain ⟨g, sR, rfl, hInv, hok⟩ := hpre
      refine hbody g sR args hInv hok _ (fun g' sR' hs' F => ?_) n
      have hR : ∀ o, (gExportSpec Inv a).post (gStore g sR) args (gStore g' sR') o := by
        intro o g'' sR'' heq
        obtain ⟨a', k, fk, hf', hc'⟩ := hhost g' sR' hs'
        obtain ⟨rfl, rfl⟩ := gStore_inj heq hf' hc'
        exact hs'
      refine ⟨⟨by simp [hrs], rfl, .inl ⟨[], by simp, hR _⟩⟩, fun vs => ?_,
        ⟨rfl, .inr (.inl ⟨rfl, hR _⟩)⟩, fun a => ⟨rfl, .inr (.inr ⟨a, rfl, hR _⟩)⟩⟩
      exact ⟨[] ++ vs, [], by simp, by simp [hrs], rfl, .inl ⟨[], by simp, hR _⟩⟩

/-! ## Import calls under a ghost contract -/

section Calls

variable {X I O C : Type} {P : Profile} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {K : GContract I G} {s : Store (Nat × G)} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post (Nat × G)}

/-- **The import call rule under a ghost contract.** -/
theorem hwp_gcall {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val} {i : Import} {g : G} {sR : Store Nat} (hs : s = gStore g sR)
    (hx : f.module.funcs[x.toNat]? = some k) (hf : sR.funcs[k]? = some fk)
    (hcode : fk.code = .host k) (he : Expand fk.type (.func ps rs)) (hn : args.length = ps.length)
    (hi : m.imports[k]? = some i) (hpre : K.pre g (calloutIn i memAddr sR args))
    (hk : ∀ sR' r, K.reply ⟨k, sR, args⟩ ⟨sR', r⟩ →
      (∀ y, R.answerIn (calloutIn i memAddr sR args) ⟨r, memOf memAddr sR'⟩ = some y → K.ans y) →
      (∀ res, r = .values res →
        HWP P (gHost m memAddr R K)
          (gStore (ansGhost R K g (calloutIn i memAddr sR args) ⟨r, memOf memAddr sR'⟩) sR') f
          (vals (us ++ res) ++ expression is) Q) ∧
      (r = .trap →
        Q (gStore (ansGhost R K g (calloutIn i memAddr sR args) ⟨r, memOf memAddr sR'⟩) sR') f
          .trap) ∧
      (∀ a, r = .throw a →
        Q (gStore (ansGhost R K g (calloutIn i memAddr sR args) ⟨r, memOf memAddr sR'⟩) sR') f
          (.throw a))) :
    HWP P (gHost m memAddr R K) s f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    have hS : gCtx m memAddr R K (Prod.fst (k, g)) = some (gImportSpec k i memAddr R K) := by
      simp [gCtx, hi]
    have hf' : s.funcs[k]? = some (FuncInst.mapH (ghostH g) fk) := by
      rw [hs, gStore_funcs, hf]; rfl
    have hc' : (FuncInst.mapH (ghostH g) fk).code = .host (k, g) := by
      simp [FuncInst.mapH, hcode, FuncCode.mapH, ghostH]
    refine Safe.callIdx (x := x)
      (S := Silmaril.Wasm.Logic.Open.stubSpec k (k, g) (gImportSpec k i memAddr R K)) hx hf'
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS n)
      ⟨⟨_, ps, rs, hf', hc', he, hn⟩, ⟨g, sR, hs, hpre⟩⟩ ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · obtain ⟨g₁, sR₁, hs₁, r, sR', hr, rfl, hrep, hans⟩ := hR
      obtain ⟨rfl, rfl⟩ := gStore_inj (hs.symm.trans hs₁) hf hcode
      obtain rfl : r = .values res := by cases r <;> simp_all [resultOutcome]
      exact (hk sR' _ hrep hans).1 res rfl n
    · obtain ⟨g₁, sR₁, hs₁, r, sR', hr, rfl, hrep, hans⟩ := hR
      obtain ⟨rfl, rfl⟩ := gStore_inj (hs.symm.trans hs₁) hf hcode
      obtain rfl : r = .trap := by cases r <;> simp_all [resultOutcome]
      exact (hk sR' _ hrep hans).2.1 rfl
    · obtain ⟨g₁, sR₁, hs₁, r, sR', hr, rfl, hrep, hans⟩ := hR
      obtain ⟨rfl, rfl⟩ := gStore_inj (hs.symm.trans hs₁) hf hcode
      obtain rfl : r = .throw y := by cases r <;> simp_all [resultOutcome]
      exact (hk sR' _ hrep hans).2.2 y rfl

end Calls

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost
