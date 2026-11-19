import ctypes as C, hashlib, json, platform, re, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
artifact=ROOT/'corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1'
assert platform.machine() == 'x86_64', 'native x86-64 check requires an x86-64 host'
receipt=json.loads(artifact.with_name('receipt.json').read_text())
record=next(x for x in receipt['outputs'] if x['object']=='libcjson.so.1')
assert hashlib.sha256(artifact.read_bytes()).hexdigest()==record['sha256']
symbols=subprocess.check_output(['readelf','-Ws',str(artifact)],text=True)
assert re.search(r'40:\s+00000000000055ad\s+38\s+FUNC\s+LOCAL\s+DEFAULT\s+12\s+suffix_object',symbols)
lib=C.CDLL(str(artifact))
class Info(C.Structure):
    _fields_=[('name',C.c_char_p),('base',C.c_void_p),('symbol',C.c_char_p),('symbol_address',C.c_void_p)]
info=Info(); dl=C.CDLL(None); dl.dladdr.argtypes=[C.c_void_p,C.POINTER(Info)];dl.dladdr.restype=C.c_int
assert dl.dladdr(C.cast(lib.cJSON_GetArraySize,C.c_void_p),C.byref(info))
address=0x55ad
expected_code=bytes.fromhex('55 48 89 e5 48 89 7d f8 48 89 75 f0 48 8b 45 f8 48 8b 55 f0 48 89 10 48 8b 45 f0 48 8b 55 f8 48 89 50 08 90 5d c3')
assert C.string_at(info.base+address,38)==expected_code
class Node(C.Structure):
    _fields_=[('next',C.c_void_p),('prev',C.c_void_p),('child',C.c_void_p),('type',C.c_int),('valuestring',C.c_void_p),('valueint',C.c_int),('valuedouble',C.c_double),('string',C.c_void_p)]
assert C.sizeof(Node)==64 and Node.next.offset==0 and Node.prev.offset==8
function=C.CFUNCTYPE(None,C.POINTER(Node),C.POINTER(Node))(info.base+address)
records=[]
for seed in range(4):
    objects=(Node*3)()
    objects[0].next = C.addressof(objects[2]) if seed % 2 else None
    objects[1].prev = C.addressof(objects[2]) if seed // 2 else None
    before=C.string_at(C.addressof(objects),C.sizeof(objects));expected=bytearray(before)
    expected[0:8]=C.addressof(objects[1]).to_bytes(8,'little')
    expected[72:80]=C.addressof(objects[0]).to_bytes(8,'little')
    function(C.pointer(objects[0]),C.pointer(objects[1]))
    after=C.string_at(C.addressof(objects),C.sizeof(objects));assert after==expected
    # Complete caller-memory equality with exactly the two specified writes;
    # neither an arbitrary footprint permission nor an assumed final heap.
    unrelated=bytearray(after);unrelated[128]^=1;assert unrelated!=expected
    missing=bytearray(after);missing[72:80]=before[72:80];assert missing!=expected
    extra=bytearray(after);extra[16]^=1;assert extra!=expected
    records.append({'seed':seed,'actual_two_writes_and_all_other_caller_bytes_preserved':True,'unrelated_mutation_rejected':True,'missing_second_write_rejected':True,'extra_field_write_rejected':True})
print(json.dumps({'artifact':str(artifact.relative_to(ROOT)),'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'actual_local_symbol':'suffix_object','address':address,'size':38,'code_hex':expected_code.hex(),'native_cases':records,'scope':'Native preflight only; no Core/context registration or semantic proof; static address is from actual ELF symbol table; no artifact rebuild/modification'},indent=2))
