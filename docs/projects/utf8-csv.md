# UTF-8 CSV wire profile

`Silmaril.Formats.Csv.Utf8` extends the strict ASCII CSV codec with non-ASCII UTF-8 field data.
It uses the comma, quote, doubled quote and CRLF productions of RFC 4180 §2.
The extension expands §2's ASCII `TEXTDATA` and selects UTF-8 for the
`text/csv` charset parameter described in §3. UTF-8 well-formedness follows
RFC 3629 §§3–4. [Strict ASCII CSV profile](rfc4180-csv.md) · [RFC 4180](https://www.rfc-editor.org/rfc/rfc4180.html#section-2)
· [RFC 4180 §3](https://www.rfc-editor.org/rfc/rfc4180.html#section-3)
· [RFC 3629](https://www.rfc-editor.org/rfc/rfc3629.html#section-3)

- Bare fields admit printable ASCII other than comma and double quote, plus
  well-formed UTF-8 encodings of non-ASCII scalars. Quoted fields additionally
  admit commas, doubled double quotes, CR and LF. Other ASCII control bytes
  and DEL are rejected in either form.
- Decoding checks UTF-8 in each unescaped field. Overlong sequences, surrogate
  encodings, out-of-range scalars, stray continuation bytes and truncated
  sequences are rejected. A sequence cannot span a field or record boundary.
- The codec preserves cell bytes without Unicode normalization. An initial
  UTF-8 BOM (`EF BB BF`) is kept as U+FEFF in the first field. [RFC 3629 §6](https://www.rfc-editor.org/rfc/rfc3629.html#section-6)
- CRLF separates records outside quotes, with an optional final CRLF. Zero
  bytes represent zero rows. A lone CRLF or a quoted empty field represents
  one row containing one empty field. A trailing comma adds an empty field,
  and ragged rows retain their distinct widths.
- Encoding validates the same field alphabet and UTF-8, quotes every field,
  and ends each emitted row with CRLF. Zero-field rows are rejected. The data
  model is lexical rows. Header interpretation, typed cells, null inference
  and named-table composition are outside this API.

`Silmaril.Formats.Csv.Utf8.Thms` exports `decode_encode` for exact lexical
round trips after successful encoding and `decode_fields_utf8` for every
field returned by the decoder. `decode_eq_ascii` agrees with the strict
decoder on all ASCII input bytes, including rejected inputs.
`encode_eq_ascii` agrees with the strict encoder when all supplied field
bytes are ASCII, including rejected rows. Encoding yields a canonical spelling,
so the round-trip law recovers the row data and field bytes.

The independent fixture harness pins CPython 3.13.5
(`6cb20a219a860eaf687b2d968b41c480c7461909`). It compares Lean and
Python reader results and canonical writer bytes for the shared subset, using
strict UTF-8, `newline=""`, doubled quotes, `QUOTE_ALL` and CRLF.
Malformed-byte fixtures are checked against Python's strict UTF-8 decoder
and the Lean wire decoder. Lean-only guards cover the profile's bare-CRLF
empty-field convention and rejection of a bare LF record separator. [CPython `_csv.c`](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/Modules/_csv.c)

```sh
lake build --wfail +Silmaril.Formats.Csv.Utf8.Tests
python3 -I scripts/csv-utf8-oracle/check.py
```
