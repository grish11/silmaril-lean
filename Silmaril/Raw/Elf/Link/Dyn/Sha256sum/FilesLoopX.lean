module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesLoop
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesErrX
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailEnd

/-! # GNU `sha256sum F1 … Fn` with refused operands: the loop on the extended process

A refused operand runs `quotef`, whose first instructions are SSE moves, so the file-error tier
is a statement about the extended process `procG XG W` (`Str9G` in the image), not `proc`.

PROVED (standard axioms):

* `ShowsX`, `LoopStepsX`, `sha_loopX`, **`sha256sum_filesX`**: `FilesLoop`'s generic operand loop
  and end-to-end statement, over `procG XG W` (the same proofs; `Inv` is any loop invariant);
* `step2b86_f`: block `0x2b86` when `digest_file` returned false (`al = 0`): `je` to the loop
  head `0x2b57`, `eax` (hence the `ok` byte `main` stores next) unchanged.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.ProcG
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Apps.Sha256sum (Bytes Outcome sha256sum diagE quotef computeLine)
open Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec

/-- An extended state shows the outcome `o` (on its view). -/
def ShowsX (o : Outcome) (z : XPS) : Prop := Shows o (z.view XG)

/-- **One iteration of the operand loop** on the extended process. -/
structure LoopStepsX (W : Silmaril.Elf.Link.Dyn.Proc.World) (w : Silmaril.Apps.Sha256sum.World)
    (Inv : List Bytes → Bytes → Bytes → Bool → XPS → Prop) (Q : XPS → Prop) : Prop where
  ok : ∀ f rest out err ok x d, w.fs f = .ok d → Inv (f :: rest) out err ok x →
    (∀ y, Inv rest (out ++ computeLine opts0 f d) err ok y → MustG XG W Q y) → MustG XG W Q x
  fail : ∀ f rest out err ok x e, w.fs f = .openErr e → Inv (f :: rest) out err ok x →
    (∀ y, Inv rest out (err ++ diagE w.prog (quotef f) e) false y → MustG XG W Q y) → MustG XG W Q x

/-- **The operand loop** on the extended process. -/
theorem sha_loopX {W : Silmaril.Elf.Link.Dyn.Proc.World} {w : Silmaril.Apps.Sha256sum.World}
    {Inv : List Bytes → Bytes → Bytes → Bool → XPS → Prop} {Q : XPS → Prop} (L : LoopStepsX W w Inv Q) :
    ∀ (ops : List Bytes) (out err : Bytes) (ok : Bool) (x : XPS),
      (∀ f ∈ ops, (∃ d, w.fs f = .ok d) ∨ ∃ e, w.fs f = .openErr e) → Inv ops out err ok x →
      (∀ y, Inv [] (out ++ outs w opts0 ops) (err ++ errs w opts0 ops) (ok && allOk w opts0 ops) y →
        MustG XG W Q y) → MustG XG W Q x := by
  intro ops
  induction ops with
  | nil =>
    intro out err ok x _ hx k
    exact k x (by simpa [outs, errs, allOk] using hx)
  | cons f rest ih =>
    intro out err ok x hops hx k
    have hrest : ∀ g ∈ rest, (∃ d, w.fs g = .ok d) ∨ ∃ e, w.fs g = .openErr e :=
      fun g hg => hops g (by simp [hg])
    rcases hops f (by simp) with ⟨d, hd⟩ | ⟨e, he⟩
    · refine L.ok f rest out err ok x d hd hx fun y hy => ih _ _ _ y hrest hy fun z hz => k z ?_
      simpa [outs, errs, allOk, List.flatMap_cons, opOut_ok hd, List.append_assoc] using hz
    · refine L.fail f rest out err ok x e he hx fun y hy => ih _ _ _ y hrest hy fun z hz => k z ?_
      simpa [outs, errs, allOk, List.flatMap_cons, opOut_fail he, List.append_assoc] using hz

/-- **`sha256sum F1 … Fn`, end to end, on the extended process** (the file-operand tiers,
readable and refused operands), conditional on its pieces as `FilesLoop.sha256sum_files`. -/
theorem sha256sum_filesX {W : Silmaril.Elf.Link.Dyn.Proc.World} {w : Silmaril.Apps.Sha256sum.World} (hw : FilesTier w)
    {Inv : List Bytes → Bytes → Bytes → Bool → XPS → Prop} {Start : XPS → Prop}
    (Reach : ∀ Q s, Start s → (∀ x, Inv w.argv.tail [] [] true x → MustG XG W Q x) → MustG XG W Q s)
    (L : ∀ Q, LoopStepsX W w Inv Q)
    (Ends : ∀ out err ok y, Inv [] out err ok y → MustG XG W (ShowsX ⟨out, err, if ok then 0 else 1⟩) y)
    (s : XPS) (hs : Start s) : MustG XG W (ShowsX (sha256sum w)) s := by
  obtain ⟨a0, ops, hargv⟩ := hw.argv
  have hops : w.argv.tail = ops := by rw [hargv]; rfl
  have hspec := sha256sum_plain w a0 ops hargv (by rw [← hops]; exact hw.ops)
    (by rw [← hops]; exact hw.plain) hw.out
  rw [hspec]
  refine Reach _ s hs fun x hx => sha_loopX (L _) w.argv.tail [] [] true x hw.opens hx fun y hy => ?_
  have := Ends _ _ _ y hy
  simpa [hops] using this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b86`: `digest_file` returned false (`al = 0`): `je` back to the loop head `0x2b57`. -/
theorem step2b86_f {W : Silmaril.Elf.Link.Dyn.Proc.World} {b : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b86#64) (hal : (u.m.core.read .rax).setWidth 8 = 0#8)
    (k : StepK W Q u (b + 0x2b57#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2b86 blk2b86_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_logic _) _
  rename_i bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2b86])) rfl
  rw [hal] at hbv
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2b86, hrip]
  rw [ite_t (by decide)]
  exact congrArg (b + ·) (by decide)

end Silmaril.Elf.Link.Dyn.Sha256sum
