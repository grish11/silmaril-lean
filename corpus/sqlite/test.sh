#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- run the sqlite3 shell (natively or under qemu-user) against the built library.
. "$(dirname "$0")/../common.sh"
start_test sqlite "$1" "$2"
t=$(mktemp -d); cp "$OBJ/libsqlite3.so" "$t/libsqlite3.so.0"; cp "$OBJ/sqlite3" "$t/"
q() { "${RUN[@]}" env LD_LIBRARY_PATH="$t" "$t/sqlite3" "$@" 2>&1; }
if [ "$ARCH" = aarch64 ]; then q() { "${RUN[@]}" -E LD_LIBRARY_PATH="$t" "$t/sqlite3" "$@" 2>&1; }; fi
check "${RUNS}sqlite3 :memory: 'select sqlite_version()'" "3.54.1" "$(q :memory: 'select sqlite_version()')"
check "${RUNS}sqlite3 :memory: 'create table t(x); insert into t values(1),(2),(3); select sum(x),group_concat(x) from t'" "6|1,2,3" \
  "$(q :memory: 'create table t(x); insert into t values(1),(2),(3); select sum(x),group_concat(x) from t')"
check "${RUNS}sqlite3 :memory: \"select hex(sha3('abc',256))\" (shell's built-in sha3 extension)" \
  "3A985DA74FE225B2045C172D6BD390BD855F086E3E9D525B46BFE24511431532" "$(q :memory: "select hex(sha3('abc',256))")"
q "$t/db" 'create table kv(k text primary key, v); insert into kv values("a",1),("b",2);' >/dev/null
check "${RUNS}sqlite3 FILE (create table, then reopen and query; json_object)" '{"k":"b","v":2}' \
  "$(q "$t/db" "select json_object('k',k,'v',v) from kv where k='b'")"
check "${RUNS}sqlite3 FILE 'pragma integrity_check'" ok "$(q "$t/db" 'pragma integrity_check')"
rm -rf "$t"
exit $TEST_FAILED
