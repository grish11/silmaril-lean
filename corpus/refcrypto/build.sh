#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- reference C implementations of standard crypto, one shared library per family:
#   libref_sha2.so        RFC 6234 code (SHA-1/224/256/384/512, HMAC, HKDF), cut out of the RFC text
#   libref_sha3.so        XKCP Standalone/CompactFIPS202/C/Keccak-readable-and-compact.c
#   libref_blake2.so      BLAKE2 ref/blake2b-ref.c + ref/blake2s-ref.c
#   libref_aes.so         rijndael-alg-fst.c 3.0 (Rijmen/Bosselaers/Barreto, original distribution)
#   libref_chacha_poly.so SUPERCOP crypto_stream/chacha20/e/ref (DJB chacha-ref) + poly1305-donna
#   libref_ed25519.so     orlp/ed25519 (copy of SUPERCOP ref10 Ed25519, own SHA-512)
#   libref_x25519.so      SUPERCOP crypto_scalarmult/curve25519/ref10
. "$(dirname "$0")/../common.sh"
start_build refcrypto "$1" "$2"
B=$BUILD
XK=XKCP-d20c8fcaecc543f816a0721d0dfc13b4cf27c14d
B2=BLAKE2-ed1974ea83433eba7b2d95c5dcd9ac33cb847913
RJ=rijndael-fst-3.0
SC=supercop-20261018
PD=poly1305-donna-e6ad6e091d30d7f4ec2d4f978be1fcfcbce72781
ED=ed25519-b1f19fab4aebe607805620d25a5e42566ce46a0e
SC_MEMBERS=($SC/include $SC/cryptoint $SC/crypto_stream/chacha20/e/ref $SC/crypto_scalarmult/curve25519/ref10)
A_RFC=$(archive rfc6234.txt 8f39f02a57bfd1da15634706724a585766e6223f77ecdaf243cad16cd3a1aa1b https://www.rfc-editor.org/rfc/rfc6234.txt)
A_XK=$(archive $XK.tar.gz 5a277d4dd8d83f7a3b411c7d22ede4c584a9c95ae5b81724f8f1db6197ea8776 https://github.com/XKCP/XKCP/archive/d20c8fcaecc543f816a0721d0dfc13b4cf27c14d.tar.gz)
A_B2=$(archive $B2.tar.gz e1d1194cde9fec0f150961cca8f3d9bdf7c5a5cbe020d1cdfb962b4887793124 https://github.com/BLAKE2/BLAKE2/archive/ed1974ea83433eba7b2d95c5dcd9ac33cb847913.tar.gz)
A_RJ=$(archive $RJ.zip a6ed142ac0bffcd10d0fdc82f9fe7e768fc4aac91aa2797ea9974252e09e998f 'https://web.archive.org/web/20051217122133id_/http://www.esat.kuleuven.ac.be/~rijmen/rijndael/rijndael-fst-3.0.zip')
A_SC=$(archive $SC.tar.xz 9a44c3e619632d140cbad436f5cebbea5f2b8d6efe752946c3e367c4c2ac8288 https://bench.cr.yp.to/supercop/supercop-20261018.tar.xz)
A_PD=$(archive $PD.tar.gz 78442221554769d557d2eb73583b409d88d83226d498c4e7caa1cc97b0488e4b https://github.com/floodyberry/poly1305-donna/archive/e6ad6e091d30d7f4ec2d4f978be1fcfcbce72781.tar.gz)
A_ED=$(archive $ED.tar.gz aedb26c46d3dc3b721ab37c5248d5c923142e4d56009a9605c470383f32ce77a https://github.com/orlp/ed25519/archive/b1f19fab4aebe607805620d25a5e42566ce46a0e.tar.gz)
unpack() {  # unpack DEST: every input below DEST (only the members the build uses from the big trees)
  mkdir -p "$1/rfc6234"; cp "$A_RFC" "$1/rfc6234/"
  tar -C "$1" -xzf "$A_XK" $XK/Standalone/CompactFIPS202/C/Keccak-readable-and-compact.c $XK/LICENSE $XK/README.markdown
  tar -C "$1" -xzf "$A_B2" $B2/ref $B2/COPYING $B2/README.md
  mkdir -p "$1/$RJ"; unzip -q "$A_RJ" -d "$1/$RJ"
  tar -C "$1" -xJf "$A_SC" "${SC_MEMBERS[@]}"
  tar -C "$1" -xzf "$A_PD"
  tar -C "$1" -xzf "$A_ED"
}
unpack "$B"
[ -n "${CORPUS_COLLECT:-}" ] && unpack /build/pristine
# RFC 6234: cut the C files out of the RFC text (local/extract-rfc6234.py; output is generated source)
python3 -I "$CORPUS/refcrypto/local/extract-rfc6234.py" "$B/rfc6234/rfc6234.txt" "$B/rfc6234" > /dev/null
info notes "RFC 6234 C files are cut out of rfc6234.txt by local/extract-rfc6234.py (generated/<arch>/rfc6234/)"
CFLAGS="$BASE_CFLAGS -fPIC -MMD"
info cflags "$CFLAGS"; info ldflags "-shared -Wl,-soname,<lib>"; info configure_args "(none)"
SHIM=$CORPUS/refcrypto/local/supercop-shim
mkdir -p "$B/obj"; cd "$B"
run() { echo "+ $*"; "$@"; info command "$*"; }
lib() {  # lib NAME "EXTRA CFLAGS" SRC...
  local name=$1 extra=$2; shift 2; local objs=() s o
  for s in "$@"; do
    o=obj/${name}__$(basename "${s%.c}").o
    run $CC $CFLAGS $extra -c "$s" -o "$o"; objs+=("$o")
  done
  run $CC -shared -Wl,-soname,$name -o "$name" "${objs[@]}"
  cp "$name" "$OUTDIR/"
}
R=rfc6234
lib libref_sha2.so "-I$R" $R/sha1.c $R/sha224-256.c $R/sha384-512.c $R/usha.c $R/hmac.c $R/hkdf.c
lib libref_sha3.so "" $XK/Standalone/CompactFIPS202/C/Keccak-readable-and-compact.c
lib libref_blake2.so "-I$B2/ref" $B2/ref/blake2b-ref.c $B2/ref/blake2s-ref.c
lib libref_aes.so "-I$RJ" $RJ/rijndael-alg-fst.c
CH=$SC/crypto_stream/chacha20/e/ref
lib libref_chacha_poly.so "-I$CH -I$SC/include -I$SC/cryptoint -I$SHIM/chacha20 -I$PD -DCRYPTO_NAMESPACE(name)=crypto_stream_chacha20_e_ref_##name" $CH/api.c $CH/e/chacha.c $PD/poly1305-donna.c
lib libref_ed25519.so "-I$ED/src" $ED/src/add_scalar.c $ED/src/fe.c $ED/src/ge.c $ED/src/key_exchange.c \
  $ED/src/keypair.c $ED/src/sc.c $ED/src/seed.c $ED/src/sha512.c $ED/src/sign.c $ED/src/verify.c
X=$SC/crypto_scalarmult/curve25519/ref10
lib libref_x25519.so "-I$X -I$SC/cryptoint -I$SHIM/x25519 -DCRYPTO_NAMESPACE(name)=crypto_scalarmult_curve25519_ref10_##name" $X/scalarmult.c $X/base.c $X/fe_0.c $X/fe_1.c \
  $X/fe_add.c $X/fe_copy.c $X/fe_cswap.c $X/fe_frombytes.c $X/fe_invert.c $X/fe_mul.c $X/fe_mul121666.c \
  $X/fe_sq.c $X/fe_sub.c $X/fe_tobytes.c
{ depfiles "$B" "$B/obj"
  printf '%s\n' "$B/rfc6234/rfc6234.txt" "$B/$XK/LICENSE" "$B/$XK/README.markdown" "$B/$B2/COPYING" "$B/$B2/README.md" \
    "$B/$RJ/README" "$B/$SC/cryptoint/LICENSE" "$B/$CH/implementors" "$B/$X/README" "$B/$X/implementors" "$B/$PD/README.md" \
    "$B/$ED/license.txt" "$B/$ED/readme.md" "$B/rfc6234/shatest.c"
} | grep -v "^$SHIM" | collect "$B" ""
