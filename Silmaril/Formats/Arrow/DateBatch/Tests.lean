module

meta import Silmaril.Formats.Arrow.DateBatch.Defs

open Silmaril Silmaril.Formats.Arrow

/-- Take both metadata messages and the record body from one producer fixture. -/
private meta def batchParts (input : KBytes) : Option (KBytes × KBytes × KBytes) := do
  let .metadata schemaLength ← (readEnvelope {} input 0).toOption | none
  let recordOffset := 8 + schemaLength
  let .metadata recordLength ← (readEnvelope {} input recordOffset).toOption | none
  let record := input.slice (recordOffset + 8) recordLength
  let message ← (readMessage {} record).toOption
  let data ← (readBody {} input (recordOffset + 8 + recordLength) message.bodyLength).toOption
  return (input.slice 8 schemaLength, record, data)

-- CPython 3.13.5 / PyArrow 26.0.1, pinned by the arrow-date-schema oracle.
private meta def date32Stream : KBytes :=
  KBytes.ofChunks 16 304
    [0xa00000000001000000078ffffffff, 0x401000000000a000800050006000c,
     0x800040000000800080000000c, 0x140010000000140000000100000004,
     0x1000100000000c000700060008, 0x40000001c0000001008010000,
     0x6000000a597e60000000300000000, 0x600060008,
     0x1400000088ffffffff, 0xc000c0008000500060016000c,
     0x180000001800040300, 0xa00080004000c0018000a0000,
     0x4000000100000003c, 0x200000000,
     0x80000000000000001, 0x1000000000000000000000010,
     0x10000000000000004, 0xffffffff000000000000000d,
     0xffffffff0000000000002b08]

private meta def date64Stream : KBytes :=
  KBytes.ofChunks 16 312
    [0xa00000000001000000070ffffffff, 0x401000000000a000800050006000c,
     0x800040000000800080000000c, 0x140010000000140000000100000004,
     0x1000100000000c000700060008, 0x4000000180000001008010000,
     0x4000400a597e60000000300000000, 0x88ffffffff0000000000000004,
     0x500060016000c0000000000000014, 0x18000403000000000c000c0008,
     0xc0018000a00000000000000000028, 0x100000003c0000000a00080004,
     0x2000000000000000000000004, 0x10000000000000000,
     0x200000000000000008, 0x40000000100000000,
     0xd0000000000000001, 0xfffffffffad9a400,
     0xdd9aa6e000, 0xffffffff]

private meta def expectedDates : DateValues.Column :=
  [some ⟨1969, 12, 31⟩, none, some ⟨2000, 2, 29⟩, some ⟨1970, 1, 1⟩]

private meta def observes (input : KBytes) : Bool :=
  match batchParts input with
  | some (schema, record, data) => (DateBatch.decode {} schema record data).toOption == some expectedDates
  | none => false

#guard observes date32Stream
#guard observes date64Stream
