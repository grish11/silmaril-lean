#!/usr/bin/env python3
"""Publish the existing read-only compiler viewer using public project evidence.

Only committed manifests and their checked public input paths are ingested. The
project adapter accepts exact row/shape/argument/kernel/axiom matches; no evidence
file is promoted and no exporter result is invented. Output is static JSON/text,
not a database server or compile service. Never pass a private project database.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
_spec = importlib.util.spec_from_file_location("cexplorer_pages", Path(__file__).with_name("cexplorer.py"))
cx = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cx)
_corpus_spec = importlib.util.spec_from_file_location("cexplorer_corpus", Path(__file__).with_name("corpus.py"))
corpus = importlib.util.module_from_spec(_corpus_spec)
_corpus_spec.loader.exec_module(corpus)


_equivalence_spec = importlib.util.spec_from_file_location("cexplorer_equivalence", Path(__file__).with_name("equivalence.py"))
equivalence = importlib.util.module_from_spec(_equivalence_spec)
_equivalence_spec.loader.exec_module(equivalence)

def export(project, output, *, include_corpus=True):
    output.mkdir(parents=True, exist_ok=True)
    (output / 'api/problems').mkdir(parents=True, exist_ok=True)
    downloads = output / 'api/artifacts'
    downloads.mkdir(parents=True, exist_ok=True)
    index = output.parent / 'compiler-artifacts/index.json'
    catalog = ('../', json.loads(index.read_bytes())['artifacts']) if index.is_file() else None
    with tempfile.TemporaryDirectory(prefix='compiler-pages-') as tmp:
        db = cx.connect(str(Path(tmp) / 'explorer.sqlite'))
        try:
            for manifest in sorted((cx.ROOT / 'examples/compiler-explorer/manifests').glob('*.json')):
                cx.ingest_manifest(db, manifest)
            matched = cx.ingest_project(db, project) if project else 0
            problems = cx.problem_list(db)
            statuses = Counter()
            for problem in problems:
                filename = hashlib.sha256(problem['id'].encode()).hexdigest() + '.json'
                problem['static_path'] = 'api/problems/' + filename
                payload = cx.problem_view(db, problem['id'], catalog)
                statuses.update(o['status'] for o in payload['obligations'])
                (output / problem['static_path']).write_text(json.dumps(payload, ensure_ascii=False) + '\n')
            for row in db.execute('SELECT sha256, content FROM artifacts'):
                (downloads / row['sha256']).write_bytes(row['content'])
            (output / 'api/problems.json').write_text(json.dumps(problems, ensure_ascii=False) + '\n')
        finally:
            db.close()
    corpus_statements = corpus.export(project, output / 'api/corpus') if include_corpus else []
    binary_statements = equivalence.export(project, output / 'api/equivalences') if include_corpus else []
    (output / 'integration.json').write_text(json.dumps({'compiler_problems': len(problems),
        'obligation_status_counts': dict(statuses), 'project_obligation_rows_read': matched,
        'scope': 'committed fixtures and separately registered unproved corpus statements; not whole-corpus coverage',
        'corpus_contextual_statements': len(corpus_statements), 'binary_equivalence_viewer_statements': len(binary_statements), 'corpus_refinement_status': 'UNPROVED',
        'interactive_compilation': False}, indent=2) + '\n')
    for name in ['index.html', 'app.js', 'view.js', 'style.css', 'corpus.js', 'equivalence.js']:
        shutil.copyfile(cx.UI / name, output / name)
    index = output / 'index.html'
    index.write_text(index.read_text().replace('</header>', '''<p class="note"><a href="../#/corpus">Corpus catalog</a> · <a href="../#/compiler">Integration status</a>.
This viewer covers committed compiler fixtures and registered corpus statements, not every corpus function. Corpus refinements are UNPROVED. Missing evidence remains missing; no compile service runs here.</p></header>'''))
    print(json.dumps({'compiler_problems': len(problems), 'corpus_contextual_statements': len(corpus_statements), 'binary_equivalence_viewer_statements': len(binary_statements),
                      'corpus_refinement_status': 'UNPROVED', 'project_obligation_rows_read': matched,
                      'output': str(output), 'evidence': 'exact public project row adapter; no invented exporter runs'}))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, help='public project database; omit for a navigation-only snapshot')
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    export(a.project, a.out)


if __name__ == '__main__':
    main()
