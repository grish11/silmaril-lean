module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Text.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Items.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Live.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Defs

/-!
# A probe reader, generic in the reader API and in the atom payload

`Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck` checks the children of a list through
memory for the n-ary reader over `MemAtom`. This topic states one reader module **for every
reader API and every atom type**: the n-ary reader `sexpR α`, the cons reader `consR α` and the
AST reader `astR (sexpSig α)`.

## The decoder

A `ProbeDec Q A` decodes two imports into reader events `REv Q A (BitVec 32)`:

* `next(h, i) -> i32` (`ProbeImports.next`): the read `read (q₂ h i) (a₂ r)` of the returned
  handle `r` (decoded at the answer, from the one `i32` result);
* `leaf(h, retptr)` (`ProbeImports.leaf`, no results): the read `read (q₃ h) (a₃ w retptr)`,
  where `a₃` reads the answer off the reply `w` (the memory **after** the answer), canonical-ABI
  style;
* `accept(h)`, decoded at the call.

`probeRoles`, `probeTraces`, `probeLang` are the roles, reader traces (every export invocation
read as `REv.enter`) and reader language (`Silmaril.Accept.Handle.readerLang` of any reader
`Rd`); `probeContract Rd d ρ L reply` is the reader contract in the fixed environment `ρ`:
accepts name members of `L`, every decoded read is valid and correct in `ρ`.

## The module `probeMod ix`

Imports `0 next : [i32 i32] → [i32]`, `1 leaf : [i32 i32] → []`, `2 accept : [i32] → []`; one
memory of one page; export `check : [i32] → []`:

```wat
(func $check (param $h i32)
  (call $leaf (call $next (local.get $h) (i32.const 0)) (i32.const 0))
  (call $accept (local.get $h)))
```

It asks for the child `0` of `h` and for the atom payload of that child, then accepts `h`. The
admitted hosts (`probeReply`) keep the code and the number of memories, may rewrite memory,
return one `i32` from `next` and nothing from `leaf` and `accept`.

## The three APIs

With a payload decoder `pay : Payload α` (the atom read off the reply of `leaf`):

* `naryProbe pay` (`sexpR α`): `next = sexp.child` (`child h i`), `leaf = sexp.atom`
  (`atom h`); accepted trees are in `firstAtoms`: lists whose first child is an atom;
* `consProbe pay` (`consR α`): `next = sexp.get` (`get(h, 0)` is `car h`, any other index
  `cdr h`), `leaf = sexp.atom`; accepted trees are in `carAtoms`: pairs whose car is an atom;
* `astProbe pay` (`astR (sexpSig α)`): `next = ast.child` (`child h i`), `leaf = ast.leaf`
  (the `tag` query of `h`, answered by a leaf tag with its payload); accepted trees are in
  `firstLeaves`: nodes whose first child is a leaf.

An unreadable reply decodes to an ill-typed answer (`handle 0` for `atom`, `count 0` for `tag`),
never a correct one.

Payloads: `bytesPay dec` reads the `list<u8>` at `retptr` (`(ptr, len)`, then the bytes) and
decodes it by `dec` (UTF-8 text for symbols and the bytes for byte strings and octet strings,
families of one atom kind); `kindPay dec` reads the record `{ bytes : list<u8>, kind : u32 }` and
decodes it by `dec kind bytes` (families of several atom kinds: every kind is readable);
`hintPay` reads the record `{ octets : list<u8>, hint : list<u8> }` of a hinted atom (a null
hint pointer is no hint); `u64Pay` reads the `u64` at `[retptr, retptr + 8)` (the canonical-ABI
return area of a `u64`), for word trees.

## A concrete host

`probeEnv c w`: host code `0` (`next`) returns `c` in the caller's store; host code `1`
(`leaf`) writes, in the caller's memory `0`, the bytes of `Live.itemsBytes w w` (the words
`8, 2, w, w` at `[0, 16)`) and returns nothing; other calls return nothing. Read through the
return pointer `0`, the `list<u8>` is the two low bytes of `w`, the kind code (`kindPay`) and
the hint pointer and length (`hintPay`) are `w`, and the `u64` is `8 + 2 * 2 ^ 32`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Probe

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.Text

/-! ## The decoder -/

/-- The named imports of the probe reader. -/
structure ProbeImports where
  next : String × String
  leaf : String × String
  accept : String × String := ("sexp", "accept")

/-- **A probe decoder**: the queries and answers of `next(h, i)` and `leaf(h, retptr)`. -/
structure ProbeDec (Q A : Type) where
  ix : ProbeImports
  /-- The query of `next(h, i)`. -/
  q₂ : BitVec 32 → BitVec 32 → Q
  /-- The answer of `next`, from its returned `i32`. -/
  a₂ : BitVec 32 → A
  /-- The query of `leaf(h, retptr)`. -/
  q₃ : BitVec 32 → Q
  /-- The answer of `leaf`, read off the reply (memory after the answer) at `retptr`. -/
  a₃ : HostReply → BitVec 32 → A

variable {Q A Y α : Type}

/-- **A read of `next` or `leaf`**, decoded at its answer. -/
def probeRead (d : ProbeDec Q A) (o : Callout) (w : HostReply) : Option (REv Q A (BitVec 32)) :=
  if o.imp = d.ix.next then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, i⟩], .values [.num ⟨.int .i32, r⟩] =>
        some (.read (d.q₂ h i) (d.a₂ r))
    | _, _ => none
  else if o.imp = d.ix.leaf then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (d.q₃ h) (d.a₃ w rp))
    | _, _ => none
  else none

/-- A call of `accept(h)`. -/
def probeAccept (ix : ProbeImports) (o : Callout) : Option (REv Q A (BitVec 32)) :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the probe reader: accepts at calls, reads at answers. -/
def probeRoles (d : ProbeDec Q A) : Roles Unit (REv Q A (BitVec 32)) Unit Unit where
  callIn := probeAccept d.ix
  answerIn := probeRead d

/-- **The reader traces of a module** through the probe roles. -/
def probeTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (d : ProbeDec Q A) : Set (List (REv Q A (BitVec 32))) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (probeRoles d)

/-- **The reader language of a module** through the probe roles, for the reader `Rd`. -/
def probeLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (Rd : Reader Q A (BitVec 32) Y) (d : ProbeDec Q A) (pol : OnBadRead Q A) (oa : OnInvalid)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) Y)) : Set Y :=
  readerLang Rd pol oa Rhos (probeTraces P Envs memIdx m d)

/-- **The reader contract** in the fixed environment `ρ`: accepts name members of `L`; every
decoded read is valid and correct in `ρ`. -/
def probeContract (Rd : Reader Q A (BitVec 32) Y) (d : ProbeDec Q A)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) Y) (L : Set Y)
    (reply : UCall Nat → UReply → Prop) : MemContract (REv Q A (BitVec 32)) where
  pre o := ∀ h, probeAccept (Q := Q) (A := A) d.ix o = some (.accept h) → ∀ t, ρ h = some t →
    t ∈ L
  ans x := ∀ q a, x = .read q a → Rd.valid ρ q ∧ Rd.ok ρ q a
  reply := reply

/-! ## The module -/

/-- The body of `check`. -/
def probeBody : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 0, .call ⟨0⟩, .intConst .i32 0, .call ⟨1⟩,
   .localGet ⟨0⟩, .call ⟨2⟩]

/-- **The module** over the imports `ix`. -/
def probeMod (ix : ProbeImports) : Module where
  types := [tySym, tyItems, tyAcc]
  imports := [⟨ix.next.1, ix.next.2, .func ⟨0⟩⟩, ⟨ix.leaf.1, ix.leaf.2, .func ⟨1⟩⟩,
    ⟨ix.accept.1, ix.accept.2, .func ⟨2⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], probeBody⟩]
  exports := [⟨"check", .func ⟨3⟩⟩]

/-- The shape of the values returned by host code `k`: one `i32` from `next`, nothing from
`leaf` and `accept`. -/
def probeShape (k : Nat) (vs : List Val) : Prop :=
  (k = 0 → ∃ c, vs = [.i32 c]) ∧ (k = 1 ∨ k = 2 → vs = [])

/-- The admitted host replies. -/
def probeReply : UCall Nat → UReply → Prop := ShapedReply probeShape

/-! ## Payloads -/

/-- An atom payload read off a reply at a return pointer (`none`: unreadable). -/
abbrev Payload (α : Type) := HostReply → BitVec 32 → Option α

/-- **The `list<u8>` at `retptr`**, decoded by `dec`. -/
def bytesPay (dec : List UInt8 → Option α) : Payload α := fun w rp =>
  (w.mem.bind fun mem => bytesList mem rp.toNat).bind dec

/-- **The `u64` at `[retptr, retptr + 8)`**, little-endian. -/
def u64Pay : Payload (BitVec 64) := fun w rp =>
  (w.mem.bind fun mem => segOf mem rp.toNat 8).bind WordAtom.le64

/-- The kind code `k` as a word (the live page written with `w = kindCode k`). -/
abbrev kindCode (k : UInt8) : BitVec 32 := BitVec.ofNat 32 (k.toNat + 256 * (0 : UInt8).toNat)

/-- **A kind-tagged `list<u8>` at `retptr`**: the record `{ bytes : list<u8>, kind : u32 }`,
i.e. `(ptr, len)` at `[retptr, retptr + 8)` and the kind code at `[retptr + 8, retptr + 12)`,
decoded by `dec kind bytes` (an atom of several kinds: the code selects the kind). -/
def kindPay (dec : BitVec 32 → List UInt8 → Option α) : Payload α := fun w rp =>
  w.mem.bind fun mem => (bytesList mem rp.toNat).bind fun bs =>
    ((segOf mem (rp.toNat + 8) 4).bind le32s).bind fun ks =>
      match ks with
      | [k] => dec k bs
      | _ => none

/-- **A hinted octet string at `retptr`**: the record `{ octets : list<u8>, hint : list<u8> }`
(`(ptr, len)` of the octets at `[retptr, retptr + 8)`, of the hint at `[retptr + 8,
retptr + 16)`); a null hint pointer is no hint. -/
def hintPay : Payload Hinted := fun w rp =>
  w.mem.bind fun mem => (bytesList mem rp.toNat).bind fun bs =>
    ((segOf mem (rp.toNat + 8) 4).bind le32s).bind fun ps =>
      match ps with
      | [p] => if p = 0 then some (none, bs) else
          (bytesList mem (rp.toNat + 8)).map fun h => (some h, bs)
      | _ => none

/-! ## The three reader APIs -/

/-- The imports of the n-ary probe. -/
def naryIx : ProbeImports := { next := ("sexp", "child"), leaf := ("sexp", "atom") }

/-- The imports of the cons probe. -/
def consIx : ProbeImports := { next := ("sexp", "get"), leaf := ("sexp", "atom") }

/-- The imports of the AST probe. -/
def astIx : ProbeImports := { next := ("ast", "child"), leaf := ("ast", "leaf") }

/-- **The n-ary probe**: `child(h, i)`, then `atom(c, retptr)`. -/
def naryProbe (pay : Payload α) : ProbeDec (SxQ (BitVec 32)) (SxA α (BitVec 32)) where
  ix := naryIx
  q₂ h i := .child h i.toNat
  a₂ := .handle
  q₃ := .atom
  a₃ w rp := match pay w rp with
    | some a => .atom a
    | none => .handle 0

/-- **The cons probe**: `get(h, i)` (`car` at `0`, else `cdr`), then `atom(c, retptr)`. -/
def consProbe (pay : Payload α) : ProbeDec (ConsQ (BitVec 32)) (ConsA α (BitVec 32)) where
  ix := consIx
  q₂ h i := if i = 0 then .car h else .cdr h
  a₂ := .handle
  q₃ := .atom
  a₃ w rp := match pay w rp with
    | some a => .atom a
    | none => .handle 0

/-- **The AST probe** at `sexpSig α`: `child(h, i)`, then `leaf(c, retptr)` (the `tag` query,
answered by a leaf tag with its payload). -/
def astProbe (pay : Payload α) : ProbeDec (AstQ (BitVec 32)) (AstA (sexpSig α) (BitVec 32)) where
  ix := astIx
  q₂ h i := .child h i.toNat
  a₂ := .handle
  q₃ := .tag
  a₃ w rp := match pay w rp with
    | some a => .tag ⟨SxTag.leaf, a⟩
    | none => .count 0

/-! ## The accepted trees -/

/-- **Lists whose first child is an atom.** -/
def firstAtoms (α : Type) : Set (SExp α) :=
  {t | ∃ cs a, t = SExp.ofList cs ∧ cs[0]? = some (.atom a)}

/-- **Pairs whose car is an atom.** -/
def carAtoms (α : Type) : Set (SExp2 α) := {t | ∃ a y, t = .cons (.atom a) y}

/-- **Nodes whose first child is a leaf.** -/
def firstLeaves (α : Type) : Set (AST (sexpSig α)) :=
  {t | ∃ v cs a ds, t = TExpr.ofList v cs ∧
    cs[0]? = some (TExpr.ofList (⟨SxTag.leaf, a⟩ : Σ t, (sexpSig α).Arg t) ds)}

/-! ## A concrete host -/

/-- **A host of the probe**: `next` returns `c`; `leaf` writes `itemsBytes w w` into memory
`0`. -/
def probeEnv (c w : BitVec 32) : SEnv UImp where
  S := Unit
  Ans _ e a _ := a = if e.target = 0 then ⟨e.store, .values [.i32 c]⟩ else
    ⟨if e.target = 1 then Live.itemsStore w w e.store else e.store, .values []⟩
  Div _ _ := False

end Silmaril.Wasm.Game.HandleAccept.MemSound.Probe
