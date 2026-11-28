module

public import Silmaril.Formats.Sqlite.Varint.Defs

/-! The byte-level varint utility is shared with the file format. Record
headers use it for serial types, and rowid leaf cells use it for payload
lengths and keys. Read offsets are relative to a bounded file view. -/
