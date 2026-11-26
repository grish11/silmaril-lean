const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const {
  Int32, Utf8, Table, tableFromArrays, tableFromIPC, tableToIPC, vectorFromArray,
} = require('apache-arrow');

const directory = process.argv[2];
if (!directory) throw new Error('usage: node generate.cjs OUTPUT_DIR');
fs.mkdirSync(directory, { recursive: true });

const expected = [
  [[-7, null, 42, -2147483648], ['é', null, '', '雪']],
  [[0, 2147483647], [null, 'tail']],
];
const batches = expected.map(([numbers, text]) => tableFromArrays({
  signed: vectorFromArray(numbers, new Int32()),
  text: vectorFromArray(text, new Utf8()),
}));
const schema = batches[0].schema;
for (const [name, table, values] of [
  ['multi', new Table(schema, batches.flatMap(batch => batch.batches)), expected],
  ['schemaOnly', new Table(schema, []), []],
]) {
  const bytes = tableToIPC(table, 'file');
  const replay = tableFromIPC(bytes);
  if (values.length === 0) {
    assert.equal(replay.numRows, 0);
  } else {
    assert.deepEqual(replay.batches.map(batch => [
      Array.from(batch.getChild('signed')), Array.from(batch.getChild('text')),
    ]), values);
  }
  fs.writeFileSync(path.join(directory, `${name}.arrow`), bytes);
}
