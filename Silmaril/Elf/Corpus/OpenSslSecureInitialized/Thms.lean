module
public import Silmaril.Elf.Corpus.OpenSslSecureInitialized.Defs
import Silmaril.Proofs.Elf.Corpus.OpenSslSecureInitialized
@[expose] public section
namespace Silmaril.Elf.Corpus.OpenSslSecureInitialized
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "CRYPTO_secure_malloc_initialized" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.OpenSslSecureInitialized.elaborates
open Silmaril.Elf.Staged.Corpus.Openssl.X8664.LibcryptoSo3 in
theorem code_bytes : Silmaril.Elf.Staged.Reader.kread K 0x1eab70 7 =
    some (Silmaril.X86.Link.Blob.valueLE code) := by decide +kernel
theorem global_identity : globalSymbol.description = .objectAddress "secure_mem_initialized" := by
  decide +kernel
open Silmaril.Elf.Staged.Corpus.Openssl.X8664.LibcryptoSo3 in
theorem dynamic_symbol_bytes : Silmaril.Elf.Staged.Reader.kread K 185672 24 =
    some 2381976568446606321608918257114426713335 := by decide +kernel
open Silmaril.Elf.Staged.Corpus.Openssl.X8664.LibcryptoSo3 in
theorem dynamic_name_bytes : Silmaril.Elf.Staged.Reader.kread K 264631 33 =
    some 45410581267131764599162406295649324396018206221417543769257734231822708593219 := by decide +kernel
/-- The checked instruction bytes' RIP-relative displacement addresses the real
four-byte local global at virtual address 0x48c278 (load bias zero). -/
theorem global_displacement : (0x1eab70 : Int) + 6 + 2758402 = 0x48c278 := by decide
end Silmaril.Elf.Corpus.OpenSslSecureInitialized
