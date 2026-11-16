module

public import Silmaril.Containers.Fixtures.Thms
public meta import Silmaril.Containers.Fixtures.Defs

/-!
# Fixtures: executable checks of the small runtime model

Checked by evaluation (`#guard`) when this module is built. They evaluate **the model**: the
loader `small.load`, flattening of layered images from content stores, integrity checking, and
the runner `Tiny.run` (whose results are runs of the model, `Thms.run_sound`). They do not run
or observe any container runtime.

* the no-op checker accepts `noop` and rejects the other fixtures;
* images without an executable program at the entry point are refused;
* a layered image flattens to the no-op image from honest stores;
* **a digest is not a proof**: with a tampered blob store (a crashing program under the no-op
  program's digest) the unchecked runtime starts the crashing program, and the checking runtime
  refuses the image instead. `toyHash` is a deliberately weak, non-cryptographic hash;
* the runner's runs of the HTTP and vsock fixtures are confined to their profiles, and the
  vsock fixture answers with its request reversed.
-/

public section

namespace Silmaril.Containers.Fixtures.Examples

open Silmaril.Containers Silmaril.Containers.Cas

/-- The events of a finite run. -/
def events? : Beh Ev → Option (List Ev)
  | .done t _ | .blocked t | .spins t => some t
  | .reactive _ => none

/-- How a finite run stopped. -/
def stop? : Beh Ev → Option Stop
  | .done _ s => some s
  | _ => none

/-- Comparing loader results. -/
instance : BEq (Except Refusal Tiny) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- Every event of a finite run is allowed by the profile. -/
def confinedB (P : Profile) (b : Beh Ev) : Bool :=
  match events? b with
  | some t => t.all fun e => P e.cap
  | none => false

/-! ## The no-op checker and the loader -/

#guard noopCheck noop
#guard !noopCheck crash
#guard !noopCheck spin
#guard !noopCheck http
#guard !noopCheck nitro

#guard small.load noop == .ok (.exit 0)
#guard small.load nitro == .ok (.vsockCompute nitroPort .reverse)

/-- No entry point. -/
def noEntry : Flat Blob := { config := {}, root := Tree.empty }

/-- The program at the entry point is not executable. -/
def notExec : Flat Blob :=
  { noop with root := Tree.empty.set ["app"] (some (.file (.prog (.exit 0)) false)) }

/-- The entry point is data. -/
def dataEntry : Flat Blob :=
  { noop with root := Tree.empty.set ["app"] (some (.file (.data [0x7f, 0x45, 0x4c, 0x46]) true)) }

#guard small.load noEntry == .error .noShape
#guard small.load notExec == .error .noShape
#guard small.load dataEntry == .error .noShape

/-! ## Layered images, content stores and integrity -/

/-- A deliberately weak, non-cryptographic hash, for the checks only. -/
def toyHash (b : Blob) : Nat := (reprStr b).length

/-- The digest of the no-op program. -/
def noopDigest : Nat := toyHash (.prog (.exit 0))

/-- Configurations and layers of the layered no-op image (digests 1 and 2). -/
def configs : Store Nat Config := fun d => if d = 1 then some noop.config else none
def layers : Store Nat (Layer Nat) :=
  fun d => if d = 2 then some [(["app"], some (.file noopDigest true))] else none

/-- The manifest of the layered no-op image. -/
def manifest : Layered Nat := ⟨1, [2]⟩

/-- Honest file contents. -/
def honest : Store Nat Blob := Store.empty.put toyHash (.prog (.exit 0))

/-- Tampered file contents: a crashing program under the no-op program's digest. -/
def tampered : Store Nat Blob := Store.empty.insert noopDigest (.prog (.crash 11))

/-- The loader of `small` on a layered image read from stores. -/
def loadLayered (blobs : Store Nat Blob) : Except Refusal Tiny :=
  (Runtime.layered ⟨configs, layers, blobs⟩ small).load manifest

#guard loadLayered honest == .ok (.exit 0)
#guard loadLayered (honest.checked toyHash) == .ok (.exit 0)
-- Unchecked, the runtime starts whatever the store returns under the digest.
#guard loadLayered tampered == .ok (.crash 11)
-- Checked, the mislabelled blob is missing, so the entry point is missing and the image refused.
#guard loadLayered (tampered.checked toyHash) == .error .noShape
-- A missing layer is a refusal.
#guard (Runtime.layered ⟨configs, Store.empty, honest⟩ small).load manifest == .error .missingBlob

/-! ## Runs of the fixtures for scripts of inputs -/

/-- A request. -/
def getRoot : List UInt8 := "GET / HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8.toList

#guard confinedB Profile.tcpOnly (Tiny.run (.httpServe httpPort okResponse) [getRoot, getRoot])
#guard !confinedB Profile.vsockOnly (Tiny.run (.httpServe httpPort okResponse) [getRoot])
#guard confinedB Profile.vsockOnly (Tiny.run (.vsockCompute nitroPort .reverse) [[1, 2, 3]])
#guard stop? (Tiny.run (.vsockCompute nitroPort .reverse) [[1, 2, 3]]) == some (.exited 0)
#guard (events? (Tiny.run (.vsockCompute nitroPort .reverse) [[1, 2, 3]])).map
  (·.contains (.send (csock .vsock) [3, 2, 1])) == some true
-- Without input the vsock service waits; it does not stop.
#guard stop? (Tiny.run (.vsockCompute nitroPort .reverse) []) == none

end Silmaril.Containers.Fixtures.Examples
