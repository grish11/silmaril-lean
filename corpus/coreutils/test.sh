#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- run the seven GNU coreutils programs (natively or under qemu-user).
. "$(dirname "$0")/../common.sh"
start_test coreutils "$1" "$2"
t=$(mktemp -d); printf 'pear\napple\n10\n9\nbanana\n' > "$t/in.txt"
x() { "${RUN[@]}" "$OBJ/$@"; }
for p in true echo cat wc head sort sha256sum; do
  check "${RUNS}$p --version | head -1" "$p (GNU coreutils) 9.12" "$(x $p --version | head -1)"
done
rc=0; x true || rc=$?; check "${RUNS}true; echo \$?" 0 "$rc"
check "${RUNS}echo -e 'a\\tb'" "$(printf 'a\tb')" "$(x echo -e 'a\tb')"
check "${RUNS}cat -n in.txt | tail -1" "$(printf '     5\tbanana')" "$(x cat -n "$t/in.txt" | tail -1)"
check "${RUNS}wc in.txt" " 5  5 23 $t/in.txt" "$(x wc "$t/in.txt")"
check "${RUNS}head -n 2 in.txt" "$(printf 'pear\napple')" "$(x head -n 2 "$t/in.txt")"
check "${RUNS}sort in.txt" "$(printf '10\n9\napple\nbanana\npear')" "$(x sort "$t/in.txt")"
check "${RUNS}sort -n in.txt | tail -2" "$(printf '9\n10')" "$(x sort -n "$t/in.txt" | tail -2)"
check "${RUNS}printf abc | sha256sum" "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad  -" "$(printf abc | x sha256sum)"
head -c 1000000 /dev/zero > "$t/zero"
check "${RUNS}sha256sum 1e6 zero bytes" "d29751f2649b32ff572b5e0a9f541ea660a50f94ff0beedfb0b692b924cc8025  $t/zero" "$(x sha256sum "$t/zero")"
rm -rf "$t"
exit $TEST_FAILED
