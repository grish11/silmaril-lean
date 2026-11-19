module
public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.Elf.Facts.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So.Bytes

/-! Seven actual SQLite build-query binary-equivalence problems. Each side must
terminate at its first ABI return, preserve callee-saved registers and every memory
location outside its explicit private stack footprint, and return the same concrete
signed-int result. Entry existence is required independently for both placements.
No source refinement, compiler correctness or desired equality is a premise.
Different code images need not be byte-identical; their immutable code is part of
their respective calling contexts. No global, heap, I/O or callee effects are allowed.
These are UNPROVED obligations, not established equivalences. See the public pair
manifest for exact observed build/configuration compatibility and exclusions. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence
open Silmaril.Project.Shapes
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .int32⟩
def meaning (value : Nat) : SysV.Meaning signature where
  Safe _ := True
  Returns _ r := r = BitVec.ofNat 32 value

def defaultO0VersionCode : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0xb1, 0x99, 0x2e, 0x00, 0x5d, 0xc3]
def defaultO0Version : Silmaril.Project.Shapes.Placement := ⟨958625, defaultO0VersionCode, 0⟩
def defaultO0ThreadsafeCode : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x5d, 0xc3]
def defaultO0Threadsafe : Silmaril.Project.Shapes.Placement := ⟨958636, defaultO0ThreadsafeCode, 0⟩
def defaultO2VersionCode : List (BitVec 8) := [0xb8, 0xb1, 0x99, 0x2e, 0x00, 0xc3]
def defaultO2Version : Silmaril.Project.Shapes.Placement := ⟨79904, defaultO2VersionCode, 0⟩
def defaultO2ThreadsafeCode : List (BitVec 8) := [0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]
def defaultO2Threadsafe : Silmaril.Project.Shapes.Placement := ⟨79920, defaultO2ThreadsafeCode, 0⟩
def defaultStrippedVersionCode : List (BitVec 8) := [0xb8, 0xb1, 0x99, 0x2e, 0x00, 0xc3]
def defaultStrippedVersion : Silmaril.Project.Shapes.Placement := ⟨79904, defaultStrippedVersionCode, 0⟩
def defaultStrippedThreadsafeCode : List (BitVec 8) := [0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]
def defaultStrippedThreadsafe : Silmaril.Project.Shapes.Placement := ⟨79920, defaultStrippedThreadsafeCode, 0⟩
def smallO0VersionCode : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0xb1, 0x99, 0x2e, 0x00, 0x5d, 0xc3]
def smallO0Version : Silmaril.Project.Shapes.Placement := ⟨934561, smallO0VersionCode, 0⟩
def smallO0ThreadsafeCode : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xc3]
def smallO0Threadsafe : Silmaril.Project.Shapes.Placement := ⟨934572, smallO0ThreadsafeCode, 0⟩
def smallO2VersionCode : List (BitVec 8) := [0xb8, 0xb1, 0x99, 0x2e, 0x00, 0xc3]
def smallO2Version : Silmaril.Project.Shapes.Placement := ⟨160048, smallO2VersionCode, 0⟩
def smallO2ThreadsafeCode : List (BitVec 8) := [0x31, 0xc0, 0xc3]
def smallO2Threadsafe : Silmaril.Project.Shapes.Placement := ⟨160064, smallO2ThreadsafeCode, 0⟩
def priorO0VersionCode : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0x14, 0x8a, 0x2e, 0x00, 0x5d, 0xc3]
def priorO0Version : Silmaril.Project.Shapes.Placement := ⟨921142, priorO0VersionCode, 0⟩
def priorO0ThreadsafeCode : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x5d, 0xc3]
def priorO0Threadsafe : Silmaril.Project.Shapes.Placement := ⟨921153, priorO0ThreadsafeCode, 0⟩

/-- Both independently enterable functions implement the same deterministic ABI
observation. The only hidden writes are the listed stack bytes below entry RSP;
`ContractStrict` forbids writes elsewhere and preserves ABI state at first return.
For O0 the eight-byte RBP save is private; optimized sides need no writable frame.
`CodeAt` is an obligation about the actual ELF, also discharged separately in Thms. -/
def statement (leftFile rightFile : Silmaril.X86.Link.Blob)
    (left right : Silmaril.Project.Shapes.Placement) (leftFrame rightFrame value : Nat) : Prop :=
  Silmaril.Elf.CodeAt leftFile left.base.toNat left.code ∧
  Silmaril.Elf.CodeAt rightFile right.base.toNat right.code ∧
  SysV.Implements Silmaril.X86.Open.isa left signature leftFrame (meaning value) ∧
  SysV.Implements Silmaril.X86.Open.isa right signature rightFrame (meaning value)

@[problem "silmaril.corpus.sqlite.equivalence.version_optimization"
  (title := "Actual SQLite sqlite3_libversion_number versionOptimization: contextual binary equivalence") ]
def Task.versionOptimization : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.F
    defaultO0Version defaultO2Version 8 0 3054001

@[problem "silmaril.corpus.sqlite.equivalence.threadsafe_optimization"
  (title := "Actual SQLite sqlite3_threadsafe threadsafeOptimization: contextual binary equivalence") ]
def Task.threadsafeOptimization : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.F
    defaultO0Threadsafe defaultO2Threadsafe 8 0 1

@[problem "silmaril.corpus.sqlite.equivalence.version_stripping"
  (title := "Actual SQLite sqlite3_libversion_number versionStripping: contextual binary equivalence") ]
def Task.versionStripping : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So.F
    defaultO2Version defaultStrippedVersion 0 0 3054001

@[problem "silmaril.corpus.sqlite.equivalence.threadsafe_stripping"
  (title := "Actual SQLite sqlite3_threadsafe threadsafeStripping: contextual binary equivalence") ]
def Task.threadsafeStripping : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So.F
    defaultO2Threadsafe defaultStrippedThreadsafe 0 0 1

@[problem "silmaril.corpus.sqlite.equivalence.version_configuration"
  (title := "Actual SQLite sqlite3_libversion_number versionConfiguration: contextual binary equivalence") ]
def Task.versionConfiguration : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So.F
    defaultO2Version smallO2Version 0 0 3054001

@[problem "silmaril.corpus.sqlite.equivalence.small_threadsafe_optimization"
  (title := "Actual SQLite sqlite3_threadsafe smallThreadsafeOptimization: contextual binary equivalence") ]
def Task.smallThreadsafeOptimization : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So.F
    smallO0Threadsafe smallO2Threadsafe 8 0 0

@[problem "silmaril.corpus.sqlite.equivalence.threadsafe_release"
  (title := "Actual SQLite sqlite3_threadsafe threadsafeRelease: contextual binary equivalence") ]
def Task.threadsafeRelease : Prop :=
  statement Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So.F Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.F
    priorO0Threadsafe defaultO2Threadsafe 8 0 1

end Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence
