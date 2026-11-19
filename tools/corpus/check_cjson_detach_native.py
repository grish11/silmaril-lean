import ctypes as C, hashlib, json, platform, re, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
artifact=ROOT/'corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1'
assert platform.machine() == 'x86_64', 'native x86-64 check requires an x86-64 host'
receipt=json.loads(artifact.with_name('receipt.json').read_text())
record=next(x for x in receipt['outputs'] if x['object']=='libcjson.so.1')
assert hashlib.sha256(artifact.read_bytes()).hexdigest()==record['sha256']
symbols=subprocess.check_output(['readelf','-Ws',str(artifact)],text=True)
assert re.search(r'149:\s+0000000000005cac\s+218\s+FUNC\s+GLOBAL\s+DEFAULT\s+12\s+cJSON_DetachItemViaPointer',symbols)
lib=C.CDLL(str(artifact))
class Info(C.Structure):
    _fields_=[('name',C.c_char_p),('base',C.c_void_p),('symbol',C.c_char_p),('symbol_address',C.c_void_p)]
info=Info(); dl=C.CDLL(None); dl.dladdr.argtypes=[C.c_void_p,C.POINTER(Info)];dl.dladdr.restype=C.c_int
assert dl.dladdr(C.cast(lib.cJSON_GetArraySize,C.c_void_p),C.byref(info))
address=0x5cac
# Extract bytes using ELF PT_LOAD mappings and compare actual mapped native code.
import struct
raw=artifact.read_bytes(); ph=struct.unpack_from('<Q',raw,32)[0]; ent,n=struct.unpack_from('<HH',raw,54)
for i in range(n):
    typ,flags,off,va,pa,fs,ms,al=struct.unpack_from('<IIQQQQQQ',raw,ph+i*ent)
    if typ==1 and va<=address and address+218<=va+fs:
        expected_code=raw[off+address-va:off+address-va+218];break
else: raise AssertionError('unmapped actual symbol')
assert C.string_at(info.base+address,218)==expected_code
class Node(C.Structure):
    _fields_=[('next',C.c_void_p),('prev',C.c_void_p),('child',C.c_void_p),('type',C.c_int),('valuestring',C.c_void_p),('valueint',C.c_int),('valuedouble',C.c_double),('string',C.c_void_p)]
assert C.sizeof(Node)==64 and Node.next.offset==0 and Node.prev.offset==8 and Node.child.offset==16
function=lib.cJSON_DetachItemViaPointer
assert C.cast(function,C.c_void_p).value==info.base+address
function.argtypes=[C.POINTER(Node),C.POINTER(Node)]; function.restype=C.c_void_p
records=[]
for seed in range(16):
    # Separate actual native objects, rotated to exercise differing address order.
    allocated=[Node() for _ in range(5)]
    objects=allocated[seed%5:]+allocated[:seed%5]
    ptr=lambda j: C.addressof(objects[j])
    assert all(ptr(j)+64<=ptr(k) or ptr(k)+64<=ptr(j) for j in range(5) for k in range(j))
    for j in range(5):
        C.memmove(ptr(j),bytes((seed*17+j*31+k)%256 for k in range(64)),64)
    objects[0].child=ptr(1);objects[1].next=ptr(2);objects[1].prev=ptr(3)
    objects[2].next=ptr(3);objects[2].prev=ptr(1);objects[3].next=None;objects[3].prev=ptr(2)
    before=b"".join(C.string_at(ptr(j),64) for j in range(5));expected=bytearray(before)
    expected[64:72]=ptr(3).to_bytes(8,'little');expected[200:208]=ptr(1).to_bytes(8,'little')
    expected[128:144]=bytes(16)
    returned=function(C.pointer(objects[0]),C.pointer(objects[2]))
    after=b"".join(C.string_at(ptr(j),64) for j in range(5))
    assert returned==ptr(2) and after==expected
    for start,length in [(64,8),(200,8),(128,8),(136,8)]:
        missing=bytearray(after);missing[start:start+length]=before[start:start+length];assert missing!=expected
    unrelated=bytearray(after);unrelated[280]^=1;assert unrelated!=expected
    records.append({'seed':seed,'pointer_return':True,'exact_four_writes_and_all320_bytes_checked':True,'missing_each_write_and_unrelated_mutation_rejected':True})
print(json.dumps({'artifact':str(artifact.relative_to(ROOT)),'sha256':hashlib.sha256(raw).hexdigest(),'actual_symbol':'cJSON_DetachItemViaPointer','address':address,'size':218,'code_hex':expected_code.hex(),'native_cases':records,'scope':'Native observations only, actual existing ELF; runtime addresses vary; no formal ABI/frame/refinement proof or artifact rebuild'},indent=2))
