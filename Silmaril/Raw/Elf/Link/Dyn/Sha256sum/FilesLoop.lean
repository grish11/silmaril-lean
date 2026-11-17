module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesSpec
public import Silmaril.Elf.Link.Dyn.Proc.Thms
public import Silmaril.Elf.Link.Dyn.Streams.Defs

/-! # GNU `sha256sum` with file operands: the operand loop and the end-to-end statements

`main` processes its operands in a loop (`for (; optind < argc; ++optind)`, `0x2b57`–`0x2b88`):
`digest_file (argv[optind], …)`; on success the result line (`0x2b8a`–`0x2c8a`), on failure
`ok = false`. The statements here are generic over the loop's invariant
`Inv rest out err ok x` ("at the loop head `x`, the operands `rest` are left; the run has handed
`out` to standard output and `err` to standard error, and `ok` holds so far"), so that the
instruction-level frame of `main` can be plugged in unchanged:

* `LoopSteps`: one iteration, for a readable operand (`out` grows by its line) and for one the file
  system refuses (`err` grows by its diagnostic, `ok` becomes false);
* `sha_loop`: the whole loop, by induction on the operands left, ends with the specification's
  per-operand fold (`FilesSpec.outs`/`errs`/`allOk`);
* `sha256sum_files`: **the end-to-end statement** of the file-operand tiers. From the start of the
  process (whatever `Start` is: the loader relation and the kernel's entry state), given main's
  start-up to the loop head (`Reach`), the iterations, and the exit path from the loop's end
  (`Ends`), every run ends showing exactly `Silmaril.Apps.Sha256sum.sha256sum w` (`Shows`).

`FilesTier w` is the class of worlds covered: no option, at least one operand, none starting with
`-`, `argv[0]` without `/` (the start-up path proved so far), standard output accepting writes,
and every operand either readable or refused at `open` (read errors after a successful open are
not covered: `digest_file`'s read loop is stated for streams without error).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec

open Silmaril.Apps.Sha256sum
open Silmaril.Elf.Link.Dyn.Proc (PState MustQ)
open Silmaril.Elf.Link.Dyn.Streams (ofSpec)

/-- The worlds of the file-operand tiers: `sha256sum F1 … Fn` (`n ≥ 1`) without options. -/
structure FilesTier (w : World) : Prop where
  argv : ∃ a0 ops, w.argv = a0 :: ops
  ops : w.argv.tail ≠ []
  plain : ∀ f ∈ w.argv.tail, Plain f
  noSlash : (47 : UInt8) ∉ w.argv0
  /-- no NUL in an argument (a C string) -/
  noNul : ∀ a ∈ w.argv, (0 : UInt8) ∉ a
  out : w.stdoutFull = false
  /-- each operand opens and reads without error, or fails to open -/
  opens : ∀ f ∈ w.argv.tail, (∃ d, w.fs f = .ok d) ∨ ∃ e, w.fs f = .openErr e

/-- The single-operand tier. -/
def OneFile (w : World) : Prop := FilesTier w ∧ w.argv.tail.length = 1

/-- A halted state shows the outcome `o`: exit status and standard output (`Ghost.done`), and
standard error (`Ghost.err`). -/
def Shows (o : Outcome) (u : PState) : Prop :=
  u.g.done = some (o.status, ofSpec o.stdout) ∧ u.g.err = ofSpec o.stderr

/-- **One iteration of the operand loop**, for each outcome of the operand's read. -/
structure LoopSteps (W : Silmaril.Elf.Link.Dyn.Proc.World) (w : World) (Inv : List Bytes → Bytes → Bytes → Bool → PState → Prop)
    (Q : PState → Prop) : Prop where
  ok : ∀ f rest out err ok x d, w.fs f = .ok d → Inv (f :: rest) out err ok x →
    (∀ y, Inv rest (out ++ computeLine opts0 f d) err ok y → MustQ W Q y) → MustQ W Q x
  fail : ∀ f rest out err ok x e, w.fs f = .openErr e → Inv (f :: rest) out err ok x →
    (∀ y, Inv rest out (err ++ diagE w.prog (quotef f) e) false y → MustQ W Q y) → MustQ W Q x

theorem opOut_ok {w : World} {o : Opts} {f d : Bytes} (h : w.fs f = .ok d) :
    opOut w o f = (computeLine o f d, [], true) := by simp [opOut, h]

theorem opOut_fail {w : World} {o : Opts} {f : Bytes} {e : Errno} (h : w.fs f = .openErr e) :
    opOut w o f = ([], diagE w.prog (quotef f) e, false) := by simp [opOut, h]

/-- **The operand loop**: from the loop head with operands `ops` left, every run reaches a loop
end whose output, diagnostics and status flag are the specification's fold over `ops`. -/
theorem sha_loop {W : Silmaril.Elf.Link.Dyn.Proc.World} {w : World} {Inv : List Bytes → Bytes → Bytes → Bool → PState → Prop}
    {Q : PState → Prop} (L : LoopSteps W w Inv Q) :
    ∀ (ops : List Bytes) (out err : Bytes) (ok : Bool) (x : PState),
      (∀ f ∈ ops, (∃ d, w.fs f = .ok d) ∨ ∃ e, w.fs f = .openErr e) → Inv ops out err ok x →
      (∀ y, Inv [] (out ++ outs w opts0 ops) (err ++ errs w opts0 ops) (ok && allOk w opts0 ops) y →
        MustQ W Q y) → MustQ W Q x := by
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

/-- **`sha256sum F1 … Fn`, end to end** (the file-operand tiers), conditional on its pieces:
`Reach` (process start to the loop head with every operand left and nothing written), the loop
iterations `L`, and `Ends` (from the loop's end, the run halts showing what the loop handed out,
with status 0 iff every operand was read). Then every run from a `Start` state ends showing
`sha256sum w`. -/
theorem sha256sum_files {W : Silmaril.Elf.Link.Dyn.Proc.World} {w : World} (hw : FilesTier w)
    {Inv : List Bytes → Bytes → Bytes → Bool → PState → Prop} {Start : PState → Prop}
    (Reach : ∀ Q s, Start s → (∀ x, Inv w.argv.tail [] [] true x → MustQ W Q x) → MustQ W Q s)
    (L : ∀ Q, LoopSteps W w Inv Q)
    (Ends : ∀ out err ok y, Inv [] out err ok y →
      MustQ W (Shows ⟨out, err, if ok then 0 else 1⟩) y)
    (s : PState) (hs : Start s) : MustQ W (Shows (sha256sum w)) s := by
  obtain ⟨a0, ops, hargv⟩ := hw.argv
  have hops : w.argv.tail = ops := by rw [hargv]; rfl
  have hspec := sha256sum_plain w a0 ops hargv (by rw [← hops]; exact hw.ops)
    (by rw [← hops]; exact hw.plain) hw.out
  rw [hspec]
  refine Reach _ s hs fun x hx => sha_loop (L _) w.argv.tail [] [] true x hw.opens hx fun y hy => ?_
  have := Ends _ _ _ y hy
  simpa [hops] using this

end Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec
