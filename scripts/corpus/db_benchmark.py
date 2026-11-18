#!/usr/bin/env python3
"""Replay an actual SQLite database as SQL into a fresh database.

This measures SQLite materialization, separately from Lean dump/export or project
validation. The SQL and database retain the input's disclosure restrictions.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sqlite3
import sys
import time


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--database', type=Path)
    p.add_argument('--sql', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.output.exists():
        p.error('output must be a new path (no overwrite)')
    if a.database:
        source = sqlite3.connect(a.database.resolve().as_uri() + '?mode=ro', uri=True)
        with a.sql.open('x') as f:
            for line in source.iterdump():
                f.write(line + '\n')
        source.close()
    sql = a.sql.read_text()
    start = time.monotonic()
    db = sqlite3.connect(a.output)
    db.executescript(sql)
    materialization_seconds = time.monotonic() - start
    integrity = db.execute('pragma quick_check').fetchall()
    if integrity != [('ok',)]:
        raise RuntimeError(integrity)
    counts = {name: db.execute('SELECT count(*) FROM "' + name.replace('"', '""') + '"').fetchone()[0]
              for (name,) in db.execute("SELECT name FROM sqlite_schema WHERE type='table' AND name NOT LIKE 'sqlite_%'")}
    db.close()
    print(json.dumps({'stage': 'sqlite-sql-materialization', 'sqlite_version': sqlite3.sqlite_version,
                      'sql_sha256': hashlib.sha256(sql.encode()).hexdigest(),
                      'sql_bytes': len(sql.encode()), 'database_bytes': a.output.stat().st_size,
                      'materialization_wall_seconds': materialization_seconds,
                      'table_counts': counts, 'quick_check': 'ok',
                      'limits': 'SQL replay only; excludes Lean elaboration, project validation and canonical SQL export.'}, indent=2))


if __name__ == '__main__':
    main()
