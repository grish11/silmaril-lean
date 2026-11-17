module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiLast
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesLoopX
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.ExitPath

/-! # GNU `sha256sum F1 … Fn` with refused operands: the operand loop on the extended process

The file-error tier (K8): every operand is readable and printed verbatim (`OpOk`) or refused at
`open` with some `errno` (`OpErr`: a plain name `quotef` shows bare). `main`'s operand loop then
writes the readable operands' lines on `stdout`, appends `prog: NAME: strerror(e)\n` to `stderr`
(`Ghost.err`) for each refused one, and returns `!ok` (0 iff none was refused).

The loop runs on the extended process `procG XG W` (a refused operand runs `quotef`, whose first
instructions are SSE moves); its `proc` pieces are lifted by `mx_lift`.

PROVED (standard axioms), from the two per-operand goals below:

* `mixed_loop`: from the call of `digest_file` on the first operand to `main`'s return
  (`MainRetG`, status `okCode`), by induction on the operands: `Task.okExt` then `loop_nextO` /
  `loop_lastO` (readable), `Task.errStep` then `step2b86_f` and `loop_head` / `loop_end` with
  `ok = 0` (refused);
* `mixed_exit`: then the end of the process (`task_exitPathG`): status, `stdout`, `stderr`.

OPEN (`Task`s; `Ext` is the memory the refused path needs at the loop's head and that a store into
`main`'s `ok` slot keeps: `program_invocation_name`, gnulib's quoting slots, the image's read-only
data and GOT, as `DigEntryE` asks):

* `Task.okExt`: a readable operand (`MultiLoop.loop_mid`) keeps `Ext`; for `Ext = ErrMem` it follows
  (`task_okExt`) from the narrower `Task.midPin`: `loop_mid` also keeps `program_invocation_name`.
  PROVED (`task_midPin`, F10: `loop_mid` exports `LibK`, the library variables kept);
* `Task.errStep`: a refused operand, from the call of `digest_file` (`0x2b81`) to its return
  (`0x2b86`, `al = 0`) with the diagnostic appended (`Task.digestOpenErrX` on the frame the loop
  provides). PROVED for `ErrMem` in `MixedErr.task_errStep` (K9: `DigErrExit.permMX` carries the
  permissions of `*missing` to the return).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.ProcG
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

/-- **A refused operand** (machine side): not starting with `-`, a plain name (gnulib shows it
bare), refused at `open` with `e`, short enough for `quotef`'s first slot. -/
structure OpErr (E : Env) (n : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) : Prop where
  nd : n.head? ≠ some 0x2d#8
  plain : QPlain n
  file : E.fs (toSpec n) = .openErr e
  fits : (Silmaril.Apps.Sha256sum.quotef (toSpec n)).length < 256

/-- An operand of the file-error tier. -/
def MOp (E : Env) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes) (n : List Byte) : Prop :=
  OpOk E dat n ∨ ∃ e, OpErr E n e

/-- The diagnostic of a refused operand. -/
def errLineM (prog n : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) : List Byte :=
  errorMsg prog (ofSpec (Silmaril.Apps.Sha256sum.quotef (toSpec n))) e

/-- What an operand contributes: (`stdout` bytes, `stderr` bytes, read). -/
def mOut (E : Env) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes) (prog n : List Byte) :
    List Byte × List Byte × Bool :=
  match E.fs (toSpec n) with
  | .openErr e => ([], errLineM prog n e, false)
  | _ => (fileLineM (dat (toSpec n)) n, [], true)

theorem mOut_ok {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {prog n : List Byte} (h : OpOk E dat n) : mOut E dat prog n = (fileLineM (dat (toSpec n)) n, [], true) := by
  simp [mOut, h.file]

theorem mOut_err {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {prog n : List Byte} {e : Silmaril.Apps.Sha256sum.Errno} (h : OpErr E n e) :
    mOut E dat prog n = ([], errLineM prog n e, false) := by
  simp [mOut, h.file]

/-- `stdout` of the operands `ops`. -/
def outsM (E : Env) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes) (prog : List Byte)
    (ops : List (Word × List Byte)) : List Byte :=
  ops.flatMap fun pn => (mOut E dat prog pn.2).1

/-- `stderr` of the operands `ops`. -/
def errsM (E : Env) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes) (prog : List Byte)
    (ops : List (Word × List Byte)) : List Byte :=
  ops.flatMap fun pn => (mOut E dat prog pn.2).2.1

/-- Whether every operand of `ops` was read. -/
def okM (E : Env) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes) (prog : List Byte)
    (ops : List (Word × List Byte)) : Bool :=
  ops.all fun pn => (mOut E dat prog pn.2).2.2

/-- The `ok` byte after the operands: unchanged if all were read, else 0. -/
def okFin (okv : Word) (b : Bool) : Word := if b then okv else 0#64

theorem okFin_zero (b : Bool) : okFin 0#64 b = 0#64 := by cases b <;> rfl

/-- `main`'s `ok` slot (`rbp - 0xd8`). -/
abbrev okSlot (s : PState) : Word := s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64

/-- **A readable operand keeps `Ext`** (open): `loop_mid` with the extension. -/
def Task.okExt (E : Env) (R : ShaRep) (W : World) (b lb kb sr sc : Word) (s : PState) (Ext : Memory → Prop) : Prop :=
  MultiImps E R W b lb kb sc → LoopCtx E W s →
  ∀ (Q : PState → Prop) (v : PState) (q p : Word) (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte)
    (g okv : Word) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes),
    LoopAtO E W b lb kb sr sc s v q p n rest X g okv → Ext v.m.memory → OpOk E dat n →
    (∀ x, LoopFrO E W b lb kb sr sc s x (b + 0x2c8a#64) q p n rest (X ++ fileLineM (dat (toSpec n)) n) g okv →
      x.g.err = v.g.err → Ext x.m.memory → MustQ W Q x) → MustQ W Q v

/-- **A refused operand** (open): from the call of `digest_file` (`0x2b81`) to its return at
`0x2b86` with `al = 0`, the diagnostic `prog: NAME: strerror(e)\n` appended to `stderr`, the
loop's invariant and `Ext` kept. -/
def Task.errStep (E : Env) (R : ShaRep) (W : World) (b lb kb sr sc : Word) (s : PState) (Ext : Memory → Prop)
    (prog : List Byte) : Prop :=
  MultiImps E R W b lb kb sc → LoopCtx E W s →
  ∀ (Q : XPS → Prop) (y : XPS) (q p : Word) (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte)
    (g okv : Word) (e : Silmaril.Apps.Sha256sum.Errno),
    LoopAtO E W b lb kb sr sc s (y.view XG) q p n rest X g okv → Ext (y.view XG).m.memory → OpErr E n e →
    (∀ z : XPS, LoopFrO E W b lb kb sr sc s (z.view XG) (b + 0x2b86#64) q p n rest X g okv →
      (z.view XG).g.err = (y.view XG).g.err ++ errLineM prog n e → Ext (z.view XG).m.memory →
      ((z.view XG).m.core.read .rax).setWidth 8 = 0#8 → MustG XG W Q z) → MustG XG W Q y

/-- **A `proc` piece on the extended process.** -/
theorem mx_lift {W : World} {Q : XPS → Prop} {y : XPS} {P : PState → Prop}
    (h : ∀ Q' : PState → Prop, (∀ t, P t → MustQ W Q' t) → MustQ W Q' (y.view XG))
    (k : ∀ z : XPS, P (z.view XG) → MustG XG W Q z) : MustG XG W Q y :=
  mustG_of_mustQ XG (s := y.view XG) (x := y.x) rfl
    (h _ fun t ht => must_done fun x' hx => k ⟨x', t.g⟩ (by rw [xview_mk hx]; exact ht))

theorem outsM_cons {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {prog : List Byte} (pn : Word × List Byte) (ops : List (Word × List Byte)) :
    outsM E dat prog (pn :: ops) = (mOut E dat prog pn.2).1 ++ outsM E dat prog ops := rfl

theorem errsM_cons {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {prog : List Byte} (pn : Word × List Byte) (ops : List (Word × List Byte)) :
    errsM E dat prog (pn :: ops) = (mOut E dat prog pn.2).2.1 ++ errsM E dat prog ops := rfl

theorem okM_cons {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {prog : List Byte} (pn : Word × List Byte) (ops : List (Word × List Byte)) :
    okM E dat prog (pn :: ops) = ((mOut E dat prog pn.2).2.2 && okM E dat prog ops) := rfl

/-- The end of the loop, after a readable last operand. -/
theorem mixed_ok_last {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s) {Ext : Memory → Prop}
    (Tok : Task.okExt E R W b lb kb sr sc s Ext) {prog : List Byte} {g : Word} {Q : XPS → Prop}
    {q p okv : Word} {n X : List Byte} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {y : XPS} (hy : LoopAtO E W b lb kb sr sc s (y.view XG) q p n [] X g okv) (hE : Ext (y.view XG).m.memory)
    (hok : okv = 0#64 ∨ okv = 1#64) (hop : OpOk E dat n)
    (k : ∀ z : XPS, MainRetG E W b lb s (z.view XG) (X ++ outsM E dat prog [(p, n)])
      (okCode (okFin okv (okM E dat prog [(p, n)]))) ((y.view XG).g.err ++ errsM E dat prog [(p, n)]) →
      MustG XG W Q z) : MustG XG W Q y := by
  refine mx_lift (P := fun t => MainRetG E W b lb s t (X ++ fileLineM (dat (toSpec n)) n) (okCode okv)
    (y.view XG).g.err) (fun Q' k' => ?_) fun z hz => k z ?_
  · exact Tok M c Q' _ q p n [] X g okv dat hy hE hop fun x hx he _ =>
      loop_lastO M c hx hok fun t ht => k' t (by rw [he] at ht; exact ht)
  · have e1 : outsM E dat prog [(p, n)] = fileLineM (dat (toSpec n)) n := by
      simp [outsM, mOut_ok (prog := prog) hop]
    have e2 : errsM E dat prog [(p, n)] = [] := by simp [errsM, mOut_ok (prog := prog) hop]
    have e3 : okM E dat prog [(p, n)] = true := by simp [okM, mOut_ok (prog := prog) hop]
    rw [e1, e2, e3, List.append_nil]; exact hz

/-- The end of the loop, after a refused last operand. -/
theorem mixed_err_last {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s) {Ext : Memory → Prop} {prog : List Byte}
    (Terr : Task.errStep E R W b lb kb sr sc s Ext prog) {g : Word} {Q : XPS → Prop}
    {q p okv : Word} {n X : List Byte} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {e : Silmaril.Apps.Sha256sum.Errno}
    {y : XPS} (hy : LoopAtO E W b lb kb sr sc s (y.view XG) q p n [] X g okv) (hE : Ext (y.view XG).m.memory)
    (hop : OpErr E n e)
    (k : ∀ z : XPS, MainRetG E W b lb s (z.view XG) (X ++ outsM E dat prog [(p, n)])
      (okCode (okFin okv (okM E dat prog [(p, n)]))) ((y.view XG).g.err ++ errsM E dat prog [(p, n)]) →
      MustG XG W Q z) : MustG XG W Q y := by
  have I := M.dig.cl.img
  have hb := M.dig.cl.hb
  refine Terr M c Q y q p n [] X g okv e hy hE hop fun z hz herr _ hal => ?_
  refine mx_lift (P := fun t => MainRetG E W b lb s t X (okCode 0#64) (z.view XG).g.err) (fun Q' k' => ?_)
    fun z' hz' => k z' ?_
  · refine step2b86_f I hb hz.body.done hz.ma hz.rip hal fun w r1 m1 g1 R1 f1 => ?_
    exact loop_end M c hz (okn := 0#64) (Or.inl rfl) r1 m1 g1 (fun r _ => R1 r) (by rw [R1, hal]; rfl) f1 k'
  · have e1 : outsM E dat prog [(p, n)] = [] := by simp [outsM, mOut_err (dat := dat) (prog := prog) hop]
    have e2 : errsM E dat prog [(p, n)] = errLineM prog n e := by
      simp [errsM, mOut_err (dat := dat) (prog := prog) hop]
    have e3 : okM E dat prog [(p, n)] = false := by simp [okM, mOut_err (dat := dat) (prog := prog) hop]
    rw [e1, e2, e3, List.append_nil, ← herr]; exact hz'

/-- A readable operand with operands left: to the next operand's `digest_file`. -/
theorem mixed_ok_next {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s) {Ext : Memory → Prop}
    (hExt : ∀ m v, Ext m → Ext (storeMem m (okSlot s) 1 v))
    (Tok : Task.okExt E R W b lb kb sr sc s Ext) {g : Word} {Q : XPS → Prop}
    {q p p' okv : Word} {n n' X : List Byte} {rest : List (Word × List Byte)}
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {y : XPS} (hy : LoopAtO E W b lb kb sr sc s (y.view XG) q p n ((p', n') :: rest) X g okv)
    (hE : Ext (y.view XG).m.memory) (hok : okv = 0#64 ∨ okv = 1#64) (hop : OpOk E dat n)
    (k : ∀ z : XPS, LoopAtO E W b lb kb sr sc s (z.view XG) (q + 8#64) p' n' rest
      (X ++ fileLineM (dat (toSpec n)) n) g okv → (z.view XG).g.err = (y.view XG).g.err →
      Ext (z.view XG).m.memory → MustG XG W Q z) : MustG XG W Q y := by
  refine mx_lift (P := fun t => LoopAtO E W b lb kb sr sc s t (q + 8#64) p' n' rest
      (X ++ fileLineM (dat (toSpec n)) n) g okv ∧ t.g.err = (y.view XG).g.err ∧ Ext t.m.memory)
    (fun Q' k' => ?_) fun z hz => k z hz.1 hz.2.1 hz.2.2
  exact Tok M c Q' _ q p n _ X g okv dat hy hE hop fun x hx he hEx =>
    loop_nextO M c hx hok fun v hv hg hm => k' v ⟨hv, by rw [hg, he], by rw [hm]; exact hExt _ _ hEx⟩

/-- A refused operand with operands left: to the next operand's `digest_file`, `ok = 0`. -/
theorem mixed_err_next {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s) {Ext : Memory → Prop}
    (hExt : ∀ m v, Ext m → Ext (storeMem m (okSlot s) 1 v)) {prog : List Byte}
    (Terr : Task.errStep E R W b lb kb sr sc s Ext prog) {g : Word} {Q : XPS → Prop}
    {q p p' okv : Word} {n n' X : List Byte} {rest : List (Word × List Byte)}
    {e : Silmaril.Apps.Sha256sum.Errno}
    {y : XPS} (hy : LoopAtO E W b lb kb sr sc s (y.view XG) q p n ((p', n') :: rest) X g okv)
    (hE : Ext (y.view XG).m.memory) (hop : OpErr E n e)
    (k : ∀ z : XPS, LoopAtO E W b lb kb sr sc s (z.view XG) (q + 8#64) p' n' rest X g 0#64 →
      (z.view XG).g.err = (y.view XG).g.err ++ errLineM prog n e →
      Ext (z.view XG).m.memory → MustG XG W Q z) : MustG XG W Q y := by
  have I := M.dig.cl.img
  have hb := M.dig.cl.hb
  refine Terr M c Q y q p n _ X g okv e hy hE hop fun z hz herr hEz hal => ?_
  refine mx_lift (P := fun t => LoopAtO E W b lb kb sr sc s t (q + 8#64) p' n' rest X g 0#64 ∧
      t.g.err = (z.view XG).g.err ∧ Ext t.m.memory) (fun Q' k' => ?_)
    fun z' hz' => k z' hz'.1 (by rw [hz'.2.1, herr]) hz'.2.2
  refine step2b86_f I hb hz.body.done hz.ma hz.rip hal fun w r1 m1 g1 R1 f1 => ?_
  exact loop_head M c hz (okn := 0#64) (Or.inl rfl) r1 m1 g1 (fun r _ => R1 r) (by rw [R1, hal]; rfl) f1
    fun v hv hg hm => k' v ⟨hv, by rw [hg], by rw [hm]; exact hExt _ _ hEz⟩

set_option maxRecDepth 4000 in
/-- **The operand loop of the file-error tier**, from the call of `digest_file` on the first of
`(p, n) :: rest` to `main`'s return with `!ok`. -/
theorem mixed_loop {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s) {Ext : Memory → Prop}
    (hExt : ∀ m v, Ext m → Ext (storeMem m (okSlot s) 1 v)) {prog : List Byte}
    (Tok : Task.okExt E R W b lb kb sr sc s Ext) (Terr : Task.errStep E R W b lb kb sr sc s Ext prog)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes} {g : Word} {Q : XPS → Prop} :
    ∀ (rest : List (Word × List Byte)) (q p : Word) (n X : List Byte) (okv : Word) (y : XPS),
      LoopAtO E W b lb kb sr sc s (y.view XG) q p n rest X g okv → Ext (y.view XG).m.memory →
      (okv = 0#64 ∨ okv = 1#64) → (∀ pn ∈ (p, n) :: rest, MOp E dat pn.2) →
      (∀ z : XPS, MainRetG E W b lb s (z.view XG) (X ++ outsM E dat prog ((p, n) :: rest))
        (okCode (okFin okv (okM E dat prog ((p, n) :: rest))))
        ((y.view XG).g.err ++ errsM E dat prog ((p, n) :: rest)) → MustG XG W Q z) →
      MustG XG W Q y := by
  intro rest
  induction rest with
  | nil =>
    intro q p n X okv y hy hE hok hops k
    rcases hops (p, n) (by simp) with hop | ⟨e, hop⟩
    · exact mixed_ok_last M c Tok hy hE hok hop k
    · exact mixed_err_last M c Terr hy hE hop k
  | cons pn rest ih =>
    obtain ⟨p', n'⟩ := pn
    intro q p n X okv y hy hE hok hops k
    have hops' : ∀ pn ∈ (p', n') :: rest, MOp E dat pn.2 := fun pn hpn => hops pn (List.mem_cons_of_mem _ hpn)
    rcases hops (p, n) (by simp) with hop | ⟨e, hop⟩
    · refine mixed_ok_next M c hExt Tok hy hE hok hop fun z hz herr hEz => ?_
      refine ih _ _ _ _ okv z hz hEz hok hops' fun z' hz' => k z' ?_
      have e1 : outsM E dat prog ((p, n) :: (p', n') :: rest) =
          fileLineM (dat (toSpec n)) n ++ outsM E dat prog ((p', n') :: rest) := by
        simp only [outsM_cons, mOut_ok hop]
      have e2 : errsM E dat prog ((p, n) :: (p', n') :: rest) = errsM E dat prog ((p', n') :: rest) := by
        simp only [errsM_cons, mOut_ok hop, List.nil_append]
      have e3 : okM E dat prog ((p, n) :: (p', n') :: rest) = okM E dat prog ((p', n') :: rest) := by
        simp only [okM_cons, mOut_ok hop, Bool.true_and]
      rw [e1, e2, e3, ← List.append_assoc, ← herr]; exact hz'
    · refine mixed_err_next M c hExt Terr hy hE hop fun z hz herr hEz => ?_
      refine ih _ _ _ _ 0#64 z hz hEz (Or.inl rfl) hops' fun z' hz' => k z' ?_
      have e1 : outsM E dat prog ((p, n) :: (p', n') :: rest) = outsM E dat prog ((p', n') :: rest) := by
        simp only [outsM_cons, mOut_err hop, List.nil_append]
      have e2 : errsM E dat prog ((p, n) :: (p', n') :: rest) =
          errLineM prog n e ++ errsM E dat prog ((p', n') :: rest) := by
        simp only [errsM_cons, mOut_err hop]
      have e3 : okFin okv (okM E dat prog ((p, n) :: (p', n') :: rest)) =
          okFin 0#64 (okM E dat prog ((p', n') :: rest)) := by
        rw [okM_cons, mOut_err hop]
        show okFin okv false = _
        rw [okFin_zero]; rfl
      rw [e1, e2, e3, ← List.append_assoc, ← herr]; exact hz'

/-- `okCode` of a final `ok` byte is a status below 256: 0 iff all operands were read. -/
theorem okCode_fin (b : Bool) : okCode (okFin 1#64 b) = if b then 0#32 else 1#32 := by
  cases b <;> rfl

/-- **The operand loop and the end of the process** (file-error tier): every run halts with
status 0 iff no operand was refused, `stdout` holding the readable operands' lines and `stderr`
(from `Y`) the diagnostics, in order. -/
theorem mixed_exit {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) (XO : ExitOk E W b lb) {s : PState} (c : LoopCtx E W s)
    {Ext : Memory → Prop} (hExt : ∀ m v, Ext m → Ext (storeMem m (okSlot s) 1 v)) {prog : List Byte}
    (Tok : Task.okExt E R W b lb kb sr sc s Ext) (Terr : Task.errStep E R W b lb kb sr sc s Ext prog)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes} {g : Word}
    {rest : List (Word × List Byte)} {q p : Word} {n : List Byte} {y : XPS}
    (hy : LoopAtO E W b lb kb sr sc s (y.view XG) q p n rest [] g 1#64) (hE : Ext (y.view XG).m.memory)
    (hops : ∀ pn ∈ (p, n) :: rest, MOp E dat pn.2) :
    MustG XG W (fun z => Ended (if okM E dat prog ((p, n) :: rest) then 0 else 1)
        (fun w => w = outsM E dat prog ((p, n) :: rest)) (z.view XG) ∧
      (z.view XG).g.err = (y.view XG).g.err ++ errsM E dat prog ((p, n) :: rest)) y := by
  refine mixed_loop M c hExt Tok Terr rest q p n [] 1#64 y hy hE (Or.inr rfl) hops fun z hz => ?_
  rw [okCode_fin] at hz
  refine mx_lift (P := fun t => Ended (if okM E dat prog ((p, n) :: rest) then 0 else 1)
      (fun w => w = outsM E dat prog ((p, n) :: rest)) t ∧
      t.g.err = (y.view XG).g.err ++ errsM E dat prog ((p, n) :: rest)) (y := z)
    (fun Q' k' => ?_) fun z' hz' => .done hz'
  have hc : (if okM E dat prog ((p, n) :: rest) = true then 0#32 else 1#32).toNat < 256 := by
    by_cases hb : okM E dat prog ((p, n) :: rest) = true <;> simp [hb]
  refine Silmaril.X86.RelIsa.Must.bind (task_exitPathG XO s (z.view XG) _ _ _ hc hz) fun t ht => k' t ?_
  obtain ⟨⟨w, hw1, hw2⟩, he⟩ := ht
  refine ⟨⟨w, ?_, by simpa using hw2⟩, he⟩
  rw [hw1]; by_cases hb : okM E dat prog ((p, n) :: rest) = true <;> simp [hb]

/-! ## The extension: what the refused path needs of the memory at the loop's head -/

/-- **The memory the refused path needs at the loop's head** (`DigEntryE`'s image and library
facts), for `main`'s stack pointer `sp`: the GOT/`%s` facts (`ShaMemK`), the read-only data
(`ShaRO`), `quotef`'s imports (`QImps`), gnulib's slots (`QSlots`, `slot0`),
`program_invocation_name` at `pinA` naming `prog` (non-private, readable; `prog` kept, apart from
`slot0`), and where these lie (away from `main`'s stack page, above the streams). -/
structure ErrMem (E : Env) (W : World) (b lb pinA : Word) (prog : List Byte) (sp : Word) (m : Memory) : Prop where
  memK : ShaMemK b lb m
  ro : ShaRO b lb m
  qimps : QImps E W b lb m
  slots : QSlots b m
  slot0 : ∀ a, Slot0 b a → m.permits .read a = true ∧ m.permits .write a = true ∧ ¬ E.S.priv m a
  progN : ProgName m pinA prog
  pinNP : ∀ j, j < 8 → ¬ E.S.priv m (pinA.toNat + j) ∧ m.permits .read (pinA.toNat + j) = true
  progk : ∀ pa, loadN m pinA 8 = some pa → ∀ j, j < prog.length + 1 →
    W.Kept (pa.toNat + j) ∧ ¬ Slot0 b (pa.toNat + j)
  pinS : ∀ j, j < 8 → pinA.toNat + j < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ pinA.toNat + j
  /-- `program_invocation_name` lies below the streams or above `main`'s frame -/
  pinLo : ∀ j, j < 8 → pinA.toNat + j < E.S.lo ∨ sp.toNat + 8 ≤ pinA.toNat + j
  keptS : ∀ a, W.Kept a → a < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ a
  lo : E.S.lo + 4096 ≤ sp.toNat

/-- `ErrMem` is kept by a change of memory outside `main`'s stack page that keeps the private memory. -/
theorem ErrMem.keepS {E : Env} {W : World} {b lb pinA : Word} {prog : List Byte} {sp : Word} {m m' : Memory}
    (h : ErrMem E W b lb pinA prog sp m)
    (hk : Keeps (fun a => a < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ a) m m') (hp : E.S.priv m' = E.S.priv m) :
    ErrMem E W b lb pinA prog sp m' := by
  have hb := h.qimps.hb
  have hI : ∀ a, ShaImg b a → a < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ a := fun a ha =>
    h.keptS a (Or.inl (by rw [h.qimps.img]; exact ha))
  have hpin : loadN m' pinA 8 = loadN m pinA 8 := loadN_keeps hk fun j hj => h.pinS j hj
  refine ⟨h.memK.keep hb (hk.mono hI), h.ro.keep (hk.mono fun a ha => hI a ⟨by omega, by omega⟩),
    h.qimps.keep (hk.mono fun a ha => hI a ha.1), h.slots.keep hb (hk.mono fun a ha => hI a ha.1),
    fun a ha => ?_, ?_, fun j hj => ?_, fun pa hpa => h.progk pa (by rw [← hpin]; exact hpa), h.pinS, h.pinLo, h.keptS, h.lo⟩
  · have hs : a < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ a := hI a (by unfold Slot0 at ha; unfold ShaImg; omega)
    obtain ⟨h1, h2, h3⟩ := h.slot0 a ha
    exact ⟨by rw [(hk a hs).2]; exact h1, by rw [(hk a hs).2]; exact h2, by rw [hp]; exact h3⟩
  · obtain ⟨pa, hpa, hc⟩ := h.progN
    exact ⟨pa, by rw [hpin]; exact hpa, cstr_keeps hk hc fun j hj => h.keptS _ (h.progk pa hpa j hj).1⟩
  · obtain ⟨h1, h2⟩ := h.pinNP j hj
    exact ⟨by rw [hp]; exact h1, by rw [(hk _ (h.pinS j hj)).2]; exact h2⟩

/-- **A store into `main`'s `ok` slot keeps `ErrMem`.** -/
theorem ErrMem.store {E : Env} {W : World} {b lb pinA : Word} {prog : List Byte} {s : PState} {m : Memory}
    (h : ErrMem E W b lb pinA prog (s.m.core.read .rsp) m) (v : Word) :
    ErrMem E W b lb pinA prog (s.m.core.read .rsp) (storeMem m (okSlot s) 1 v) := by
  have hlo := h.lo
  have e28 : (okSlot s).toNat = (s.m.core.read .rsp).toNat - 224 :=
    (fp_neg _ 0xd8 (by omega) (by decide) (by decide)).trans (by omega)
  refine h.keepS (storeMem_keeps fun x hx => by rw [e28]; omega)
    (E.S.priv_keep _ _ (storeMem_keeps fun x hx => by have := E.S.priv_lo _ _ hx; rw [e28]; omega))

/-- **The file-error tier from the loop's head, with `ErrMem`**: `mixed_exit` for the extension
the refused path needs (`ErrMem.store`), conditional on `Task.okExt` and `Task.errStep` for it. -/
theorem mixed_exitE {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc pinA : Word}
    (M : MultiImps E R W b lb kb sc) (XO : ExitOk E W b lb) {s : PState} (c : LoopCtx E W s) {prog : List Byte}
    (Tok : Task.okExt E R W b lb kb sr sc s (ErrMem E W b lb pinA prog (s.m.core.read .rsp)))
    (Terr : Task.errStep E R W b lb kb sr sc s (ErrMem E W b lb pinA prog (s.m.core.read .rsp)) prog)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes} {g : Word}
    {rest : List (Word × List Byte)} {q p : Word} {n : List Byte} {y : XPS}
    (hy : LoopAtO E W b lb kb sr sc s (y.view XG) q p n rest [] g 1#64)
    (hE : ErrMem E W b lb pinA prog (s.m.core.read .rsp) (y.view XG).m.memory)
    (hops : ∀ pn ∈ (p, n) :: rest, MOp E dat pn.2) :
    MustG XG W (fun z => Ended (if okM E dat prog ((p, n) :: rest) then 0 else 1)
        (fun w => w = outsM E dat prog ((p, n) :: rest)) (z.view XG) ∧
      (z.view XG).g.err = (y.view XG).g.err ++ errsM E dat prog ((p, n) :: rest)) y :=
  mixed_exit M XO c (fun _ v h => h.store v) Tok Terr hy hE hops

/-! ## A readable operand and `ErrMem` -/

/-- The eight bytes of `program_invocation_name`. -/
def PinCell (pinA : Word) (a : Nat) : Prop := pinA.toNat ≤ a ∧ a < pinA.toNat + 8

/-- **A readable operand keeps `program_invocation_name`**: `MultiLoop.loop_mid` (whose run
keeps the kept memory, exported) also keeps the eight bytes at `pinA` and their non-privacy, when
they lie below the streams or above `main`'s frame. PROVED (`task_midPin`, F10): `digest_file`'s
and the result line's library calls keep the library's variables (`LibK`, exported by `DigExit`
and `PrintExit`); `free` keeps every mapped non-private byte outside the block it releases
(`FreeRet`, with the live blocks in `Ghost.blocks`). -/
def Task.midPin (E : Env) (R : ShaRep) (W : World) (b lb kb sr sc : Word) (s : PState) (pinA : Word) : Prop :=
  MultiImps E R W b lb kb sc → LoopCtx E W s →
  ∀ (Q : PState → Prop) (v : PState) (q p : Word) (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte)
    (g okv : Word) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes),
    LoopAtO E W b lb kb sr sc s v q p n rest X g okv → OpOk E dat n →
    (∀ j, j < 8 → ¬ E.S.priv v.m.memory (pinA.toNat + j) ∧ v.m.memory.permits .read (pinA.toNat + j) = true) →
    (∀ j, j < 8 → pinA.toNat + j < E.S.lo ∨ (s.m.core.read .rsp).toNat + 8 ≤ pinA.toNat + j) →
    (∀ x, LoopFrO E W b lb kb sr sc s x (b + 0x2c8a#64) q p n rest (X ++ fileLineM (dat (toSpec n)) n) g okv →
      x.g.err = v.g.err → Keeps W.Kept v.m.memory x.m.memory → Keeps (PinCell pinA) v.m.memory x.m.memory →
      (∀ j, j < 8 → ¬ E.S.priv x.m.memory (pinA.toNat + j)) → MustQ W Q x) → MustQ W Q v

/-- `ErrMem` is kept by a change of memory keeping the kept memory and `program_invocation_name`. -/
theorem ErrMem.keepK {E : Env} {W : World} {b lb pinA : Word} {prog : List Byte} {sp : Word} {m m' : Memory}
    (h : ErrMem E W b lb pinA prog sp m) (hapart : PrivApart E W) (hK : Keeps W.Kept m m')
    (hP : Keeps (PinCell pinA) m m') (hnp : ∀ j, j < 8 → ¬ E.S.priv m' (pinA.toNat + j)) :
    ErrMem E W b lb pinA prog sp m' := by
  have hb := h.qimps.hb
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [h.qimps.img]; exact ha)
  have hpin : loadN m' pinA 8 = loadN m pinA 8 := loadN_keeps hP fun j hj => ⟨by omega, by omega⟩
  refine ⟨h.memK.keep hb (hK.mono hImgK), h.ro.keep (hK.mono fun a ha => hImgK a ⟨by omega, by omega⟩),
    h.qimps.keep (hK.mono fun a ha => hImgK a ha.1), h.slots.keep hb (hK.mono fun a ha => hImgK a ha.1),
    fun a ha => ?_, ?_, fun j hj => ⟨hnp j hj, ?_⟩, fun pa hpa => h.progk pa (by rw [← hpin]; exact hpa),
    h.pinS, h.pinLo, h.keptS, h.lo⟩
  · have hk : W.Kept a := hImgK a (by unfold Slot0 at ha; unfold ShaImg; omega)
    obtain ⟨h1, h2, -⟩ := h.slot0 a ha
    exact ⟨by rw [(hK a hk).2]; exact h1, by rw [(hK a hk).2]; exact h2, fun hp => hapart _ _ hk hp⟩
  · obtain ⟨pa, hpa, hc⟩ := h.progN
    exact ⟨pa, by rw [hpin]; exact hpa, cstr_keeps hK hc fun j hj => (h.progk pa hpa j hj).1⟩
  · rw [(hP _ ⟨by omega, by omega⟩).2]; exact (h.pinNP j hj).2

/-- **`Task.midPin`, proved.** -/
theorem task_midPin {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} {s : PState} {pinA : Word} :
    Task.midPin E R W b lb kb sr sc s pinA := by
  intro M c Q v q p n rest X g okv dat hv hop hpin hloc k
  refine loop_mid M c hv hop fun x hx herr hK hS hL => k x hx herr hK ?_ ?_
  · intro a ha
    obtain ⟨h1, h2⟩ := ha
    have hj := hpin (a - pinA.toNat) (by omega)
    have hl := hloc (a - pinA.toNat) (by omega)
    rw [show pinA.toNat + (a - pinA.toNat) = a by omega] at hj hl
    rcases hl with hl | hl
    · by_cases hk : W.Kept a
      · exact hK a hk
      · exact hL.1 a ⟨hl, hk, hj.1, hj.2⟩
    · exact hS a hl
  · intro j hj hp
    rcases hloc j hj with hl | hl
    · by_cases hk : W.Kept (pinA.toNat + j)
      · exact M.apart _ _ hk hp
      · exact hL.2 _ ⟨hl, hk, (hpin j hj).1, (hpin j hj).2⟩ hp
    · have := E.S.priv_lo _ _ hp
      have := c.lo
      omega

/-- **`Task.okExt` for `ErrMem` from `Task.midPin`.** -/
theorem task_okExt {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc pinA : Word} {s : PState} {prog : List Byte}
    (T : Task.midPin E R W b lb kb sr sc s pinA) :
    Task.okExt E R W b lb kb sr sc s (ErrMem E W b lb pinA prog (s.m.core.read .rsp)) := by
  intro M c Q v q p n rest X g okv dat hv hE hop k
  exact T M c Q v q p n rest X g okv dat hv hop hE.pinNP hE.pinLo fun x hx herr hK hP hnp =>
    k x hx herr (hE.keepK M.apart hK hP hnp)

end Silmaril.Elf.Link.Dyn.Sha256sum
