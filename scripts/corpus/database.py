#!/usr/bin/env python3
"""Build a corpus metadata database; ELF bytes remain in ordinary Git.

Optionally copy an existing project database using SQLite backup before adding
the corpus tables. Never modifies the input database or overwrites output.
"""
import argparse
import json
import re
from pathlib import Path
import sqlite3
import subprocess
from census import report_relative_path
from matrix import ROOT, digest, inventory


def artifact_census(root, artifact):
    """Load only evidence for this exact artifact and receipt, when available."""
    path = root / 'corpus/census' / report_relative_path(artifact['path'])
    if not path.exists():
        return None
    text = path.read_text()
    report = json.loads(text)
    if (report['sha256'] != artifact['sha256'] or report['path'] != artifact['path'] or
            report['identity']['receipt_sha256'] != artifact['receipt_sha256']):
        raise ValueError(f'{path}: census artifact or receipt identity mismatch')
    return text


def measurement_runs(paths):
    """Merge repeated references to one immutable run; reject conflicting writers."""
    runs = {}
    for path in paths:
        run = json.loads(path.read_text())
        key = run['run_id']
        if key in runs and runs[key] != run:
            raise ValueError(f'conflicting measurements for run {key}')
        runs[key] = run
    return runs.values()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--base', type=Path, help='optional existing project database; disclosure restrictions carry over')
    p.add_argument('--source-rev', help='public Git commit for immutable artifact/source links (Pages passes GITHUB_SHA)')
    a = p.parse_args()
    if a.source_rev and not re.fullmatch(r'[0-9a-f]{40}', a.source_rev):
        p.error('--source-rev must be a full lowercase Git commit SHA')
    a.output.touch(exist_ok=False)
    db = sqlite3.connect(a.output)
    if a.base:
        source = sqlite3.connect(a.base.resolve().as_uri() + '?mode=ro', uri=True)
        source.backup(db)
        source.close()
    data = inventory(ROOT)
    formal = json.loads((ROOT / 'corpus/measurements/formal-functions/checks.json').read_text())['statements']
    revision = a.source_rev or subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    with db:
        db.executescript('''
CREATE TABLE corpus_meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE corpus_artifacts(
 id TEXT PRIMARY KEY, project TEXT NOT NULL, version TEXT NOT NULL,
 target TEXT NOT NULL, optimization TEXT NOT NULL, stripping TEXT NOT NULL,
 name TEXT NOT NULL, sha256 TEXT NOT NULL, path TEXT NOT NULL,
 source_id TEXT NOT NULL, build_id TEXT NOT NULL, metadata TEXT NOT NULL,
 census TEXT, sources TEXT NOT NULL);
CREATE INDEX corpus_identity ON corpus_artifacts(project,version,target,optimization,stripping);
CREATE INDEX corpus_hash ON corpus_artifacts(sha256);
CREATE INDEX corpus_browser ON corpus_artifacts(project,version,target,optimization,stripping,name,id,sha256,json_extract(metadata,'$.lean_status'),json_extract(metadata,'$.functional_equivalence_statements'),json_extract(metadata,'$.contextual_c_to_elf_statements'),json_extract(metadata,'$.build.configuration'));
CREATE INDEX corpus_configuration_browser ON corpus_artifacts(json_extract(metadata,'$.build.configuration'),project,version,target,optimization,stripping,name,id,sha256,json_extract(metadata,'$.lean_status'),json_extract(metadata,'$.functional_equivalence_statements'),json_extract(metadata,'$.contextual_c_to_elf_statements'));
CREATE TABLE corpus_functions(
 artifact TEXT NOT NULL, ordinal INTEGER NOT NULL, symbol TEXT NOT NULL,
 address INTEGER NOT NULL, size INTEGER NOT NULL, mapping TEXT NOT NULL,
 PRIMARY KEY(artifact,ordinal));
CREATE INDEX corpus_function_name ON corpus_functions(artifact,symbol);
CREATE TABLE corpus_timings(run_id TEXT PRIMARY KEY, build_id TEXT, stage TEXT NOT NULL, metadata TEXT NOT NULL);
''')
        db.executemany('INSERT INTO corpus_meta VALUES(?,?)', [('schema', 'corpus.catalog.v1'), ('revision', revision),
            ('artifact_rows', str(data['artifact_rows'])), ('unique_content_hashes', str(data['unique_content_hashes'])),
            ('binary_viewer_statements', str(data['binary_viewer_statement_count'])),
            *[(kind + '_statements', str(count)) for kind, count in data['formal_statement_counts'].items()]])
        for artifact in data['artifacts']:
            key = digest([artifact['build_id'], artifact['stripping'], artifact['path']])
            path = Path(artifact['path'])
            canonical = path.is_relative_to('corpus/elf')
            census = artifact_census(ROOT, artifact)
            if canonical:
                sources = [{'path': 'corpus/' + artifact['project'] + '/upstream.sha256',
                            'kind': 'canonical included upstream file hash inventory'}]
                function_path = ROOT / 'corpus' / artifact['project'] / 'funcmap' / artifact['build']['target'].removesuffix('-linux-gnu') / (path.name + '.json')
                functions = json.loads(function_path.read_text())['functions'] if function_path.exists() else []
                context_path = function_path.parent.parent.parent / 'tv' / function_path.parent.name / (path.name + '.tsv')
                contexts = {}
                if context_path.exists():
                    artifact['source_mapping_evidence'] = json.loads(context_path.read_text().splitlines()[0].removeprefix('# '))
                    for line in context_path.read_text().splitlines():
                        if line.startswith('#') or not line:
                            continue
                        fields = line.split('\t')
                        contexts[fields[0]] = {'blockers': fields[-1].split(','), 'decomposition': fields[3],
                                               'status': 'context only; no parsed/lowered C semantics or instantiated TV statement'}
                for function in functions:
                    function['tv_context'] = contexts.get(function['symbol'], {'status': 'no context row found'})
            else:
                artifact['source_mapping_evidence'] = 'paired binary addresses only; no C source binding generated'
                profile = ROOT / path.parent.parent
                sources = json.loads((profile / 'build.json').read_text())['included_source_files']
                functions = json.loads((profile / (path.name + '.pair.json')).read_text())['unstripped_function_symbols']
                for run_path in (profile / 'runs').glob('*.json'):
                    run = json.loads(run_path.read_text())
                    db.execute('INSERT OR IGNORE INTO corpus_timings VALUES(?,?,?,?)',
                               (run['run_id'], artifact['build_id'], run['stage'], json.dumps(run)))
            db.execute('INSERT INTO corpus_artifacts VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)',
                (key, artifact['project'], artifact['version'], artifact['build']['target'], artifact['optimization'],
                 artifact['stripping'], path.name, artifact['sha256'], artifact['path'], artifact['source_id'], artifact['build_id'],
                 json.dumps(artifact), census, json.dumps(sources)))
            for ordinal, function in enumerate(functions):
                concrete = [s for s in formal if s.get('function_symbol') == function.get('symbol', function.get('name'))
                            and artifact['path'] in s['artifact_sha256']
                            and ('function_address' not in s or function['value'] == s['function_address'])
                            and ('function_addresses' not in s or function['value'] == s['function_addresses'][artifact['path']])
                            and ('function_size' not in s or function['size'] == s['function_size'])]
                if concrete:
                    function['formal_statements'] = [{k: s[k] for k in ['kind', 'status', 'declaration', 'root', 'viewer_kind'] if k in s} for s in concrete]
                contextual = [s for s in concrete if s['kind'] == 'contextual_c_to_elf']
                if contextual:
                    function['tv_context'] = {
                        'status': 'concrete contextual C-to-ELF statement; stated-unproved',
                        'statements': [{k: s[k] for k in ['kind', 'status', 'declaration', 'root', 'viewer_kind'] if k in s} for s in contextual]}
                db.execute('INSERT INTO corpus_functions VALUES(?,?,?,?,?,?)', (key, ordinal,
                    function.get('symbol', function.get('name')), function['value'], function['size'], json.dumps(function)))
        baseline_paths = list((ROOT / 'corpus/census/runs').glob('*.json'))
        baseline_paths += list((ROOT / 'corpus/measurements').glob('*/runs/*.json'))
        for run in measurement_runs(baseline_paths):
            db.execute('INSERT INTO corpus_timings VALUES(?,?,?,?)', (run['run_id'], None, run['stage'], json.dumps(run)))
    # Keep the navigation working set independent of large input/hash receipts.
    # Full immutable receipts remain available by run_id on explicit expansion.
    with db:
        db.execute("CREATE TABLE corpus_timing_summary(run_id TEXT PRIMARY KEY, build_id TEXT, stage TEXT NOT NULL, wall_seconds REAL, peak_rss_kib INTEGER, exit_code INTEGER)")
        db.execute("CREATE INDEX corpus_timing_summary_build ON corpus_timing_summary(build_id,stage,run_id)")
        for run_id, build_id, stage, metadata in db.execute('SELECT * FROM corpus_timings').fetchall():
            run = json.loads(metadata)
            db.execute('INSERT INTO corpus_timing_summary VALUES(?,?,?,?,?,?)',
                       (run_id, build_id, stage, run.get('wall_seconds'), run.get('peak_rss_kib'), run.get('exit_code')))
    assert db.execute('PRAGMA quick_check').fetchall() == [('ok',)]
    print(json.dumps({'artifacts': data['artifact_rows'], 'unique_content_hashes': data['unique_content_hashes'],
                      'function_rows': db.execute('SELECT count(*) FROM corpus_functions').fetchone()[0],
                      'database': str(a.output), 'elf_bytes_embedded': False}))
    db.close()


if __name__ == '__main__':
    main()
