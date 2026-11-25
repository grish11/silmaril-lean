const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const { join, resolve } = require('node:path');

const upstream = resolve(process.argv[2], 'quint/dist/src');
const { newIdGenerator } = require(join(upstream, 'idGenerator'));
const { parse } = require(join(upstream, 'parsing/quintParserFrontend'));
const { fileSourceResolver } = require(join(upstream, 'parsing/sourceResolver'));
const { newRng } = require(join(upstream, 'rng'));
const { Evaluator } = require(join(upstream, 'runtime/impl/evaluator'));
const { rv } = require(join(upstream, 'runtime/impl/runtimeValue'));
const { newTraceRecorder } = require(join(upstream, 'runtime/trace'));

const oracle = require('./oracle.json');

function sorted(values) {
  return values.map(value => JSON.stringify(value)).sort();
}

// TLC's DOT dump identifies the initial nodes by their fill style. Labels contain
// the integer variable assignments, and edges include explicit Next self-loops.
function readTlcGraph(name, variables) {
  const dot = readFileSync(join(process.argv[3], name + '.dot'), 'utf8');
  const nodes = new Map();
  const initial = [];
  for (const [, id, label, attributes] of dot.matchAll(/^(-?\d+) \[label="([^"]*)"(.*)$/gm)) {
    const fields = new Map([...label.matchAll(/(\w+) = (-?\d+)/g)]
      .map(([, variable, value]) => [variable, Number(value)]));
    assert.deepEqual([...fields.keys()].sort(), [...variables].sort(), name + ': TLC state fields');
    const state = variables.map(variable => fields.get(variable));
    nodes.set(id, state);
    if (attributes.includes('style = filled')) initial.push(state);
  }

  const transitions = [];
  for (const [, from, to] of dot.matchAll(/^(-?\d+) -> (-?\d+) \[/gm)) {
    assert.ok(nodes.has(from) && nodes.has(to), name + ': missing TLC node');
    transitions.push([nodes.get(from), nodes.get(to)]);
  }
  return { states: [...nodes.values()], initial, transitions };
}

for (const [name, { variables, states, initial, transitions }] of Object.entries(oracle)) {
  const filename = name + '.qnt';
  const source = join(__dirname, filename);
  const lookupPath = fileSourceResolver().lookupPath(__dirname, filename);
  const parsed = parse(newIdGenerator(), source, lookupPath, readFileSync(source, 'utf8'));
  assert.deepEqual(parsed.errors, [], name + ': Quint parser errors');
  const module = parsed.modules.find(module => module.name === name);
  const init = module.declarations.find(decl => decl.kind === 'def' && decl.name === 'init');
  const step = module.declarations.find(decl => decl.kind === 'def' && decl.name === 'step');
  const rng = newRng(0n);
  const evaluator = new Evaluator(parsed.table, newTraceRecorder(0, rng), rng);

  // A run must consume exactly the one expected choice, or none for deterministic actions.
  function evaluate(action, choice) {
    let draws = 0;
    evaluator.ctx.rand = bound => {
      assert.equal(bound, 2n, name + ': choice bound');
      assert.ok(choice !== undefined && draws === 0, name + ': unexpected choice');
      draws += 1;
      return choice;
    };
    const result = evaluator.evaluate(action.expr).unwrap();
    assert.equal(draws, choice === undefined ? 0 : 1, name + ': choice count');
    assert.equal(result.kind, 'bool');
    if (!result.value) return null;

    evaluator.shift();
    const record = evaluator.ctx.varStorage.asRecord().toOrderedMap();
    assert.deepEqual([...record.keys()].sort(), [...variables].sort(), name + ': written variables');
    return variables.map(variable => Number(record.get(variable).toInt()));
  }

  assert.deepEqual([evaluate(init)], initial, name + ': initial states');
  const choices = name === 'BitPair' ? [0n, 1n] : [undefined];
  const observed = new Set();
  const domain = new Set(sorted(states));
  for (const state of states) {
    const inputs = variables.map((variable, i) => [variable, rv.mkInt(state[i])]);
    for (const choice of choices) {
      evaluator.updateState(rv.toQuintEx(rv.mkRecord(inputs)));
      const successor = evaluate(step, choice);
      if (successor !== null) {
        assert.ok(domain.has(JSON.stringify(successor)),
          name + ': successor outside the bounded domain');
        observed.add(JSON.stringify([state, successor]));
      }
    }
  }
  assert.deepEqual([...observed].sort(), sorted(transitions),
    name + ': complete bounded step relation');
  const tlc = readTlcGraph(name, variables);
  assert.deepEqual(sorted(tlc.states), sorted(states), name + ': TLC reachable states');
  assert.deepEqual(sorted(tlc.initial), sorted(initial), name + ': TLC initial states');
  assert.deepEqual(sorted(tlc.transitions), sorted(transitions), name + ': TLC step relation');
  console.log(name + ': Quint and TLC agree on ' + initial.length + ' initial state and ' +
    transitions.length + ' transitions over ' + states.length + ' states');
}
