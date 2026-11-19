# Function stripping-equivalence statements

Four additional `mi_version` problems compare actual x86_64 O0, Og, O1 and O3
stripped/unstripped pairs. Each actual function implements the same deterministic
System V int32 result meaning (219), with eight writable stack bytes, preserved
callee-saved registers, first-return termination and no other memory effects.

The paired executable-section/address receipts identify stripped addresses.
Eight independent kernel `CodeAt` theorems bind the actual ELF bytes. The
formal registry hashes both ELFs, the Lean modules and paired metadata.
No stripped symbol table is invented; matching bytes or names is not a semantic
proof. All four obligations are stated-unproved. Total binary-equivalence
statements become five, while these binary statements do not add distinct source functions.

Measured root check: `runs/6e869c39-a1b8-452a-83d0-b62975f10c69.json`.
