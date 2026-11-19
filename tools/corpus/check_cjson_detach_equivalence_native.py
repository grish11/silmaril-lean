import ctypes as C, hashlib, json, platform, re, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
assert platform.machine() == 'x86_64', 'requires x86-64 host'
import struct
class Info(C.Structure):
    _fields_=[('name',C.c_char_p),('base',C.c_void_p),('symbol',C.c_char_p),('symbol_address',C.c_void_p)]
dl=C.CDLL(None); dl.dladdr.argtypes=[C.c_void_p,C.POINTER(Info)];dl.dladdr.restype=C.c_int
functions=[];identities=[]
for name,address,size in [
 ('corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1',0x5cac,218),
 ('corpus/elf/cjson/x86_64/libcjson.so.1',0x4360,131)]:
    artifact=ROOT/name;raw=artifact.read_bytes()
    receipt=json.loads(artifact.with_name('receipt.json').read_text())
    record=next(x for x in receipt['outputs'] if x['object']=='libcjson.so.1')
    assert hashlib.sha256(raw).hexdigest()==record['sha256']
    lib=C.CDLL(str(artifact));fn=lib.cJSON_DetachItemViaPointer;info=Info()
    assert dl.dladdr(C.cast(fn,C.c_void_p),C.byref(info))
    assert C.cast(fn,C.c_void_p).value==info.base+address
    ph=struct.unpack_from('<Q',raw,32)[0];ent,n=struct.unpack_from('<HH',raw,54)
    for j in range(n):
        typ,flags,off,va,pa,fs,ms,al=struct.unpack_from('<IIQQQQQQ',raw,ph+j*ent)
        if typ==1 and flags&1 and va<=address and address+size<=va+fs:
            expected_code=raw[off+address-va:off+address-va+size];break
    else:raise AssertionError('missing executable bytes')
    assert C.string_at(info.base+address,size)==expected_code
    functions.append((lib,fn))
    identities.append({'artifact':name,'sha256':record['sha256'],'address':address,'size':size,'code_sha256':hashlib.sha256(expected_code).hexdigest()})
class Node(C.Structure):
    _fields_=[('next',C.c_void_p),('prev',C.c_void_p),('child',C.c_void_p),('type',C.c_int),('valuestring',C.c_void_p),('valueint',C.c_int),('valuedouble',C.c_double),('string',C.c_void_p)]
assert C.sizeof(Node)==64 and Node.next.offset==0 and Node.prev.offset==8 and Node.child.offset==16
for _,function in functions:
    function.argtypes=[C.POINTER(Node),C.POINTER(Node)];function.restype=C.c_void_p
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
    outcomes=[]
    for _,function in functions:
        for j in range(5):C.memmove(ptr(j),before[j*64:(j+1)*64],64)
        returned=function(C.pointer(objects[0]),C.pointer(objects[2]))
        after=b"".join(C.string_at(ptr(j),64) for j in range(5))
        assert returned==ptr(2) and after==expected
        outcomes.append((returned,after))
    assert outcomes[0]==outcomes[1]
    for start,length in [(64,8),(200,8),(128,8),(136,8)]:
        missing=bytearray(after);missing[start:start+length]=before[start:start+length];assert missing!=expected
    unrelated=bytearray(after);unrelated[280]^=1;assert unrelated!=expected
    records.append({'seed':seed,'pointer_return':True,'exact_four_writes_and_all320_bytes_checked':True,'missing_each_write_and_unrelated_mutation_rejected':True})
print(json.dumps({'artifacts':identities,'native_pairs':records,'scope':'Finite existing-ELF native pair observations only; identical caller bytes/addresses on each side, exact final four pointer words/all320 bytes; no equivalence proof, formal ABI/frame proof or artifact rebuild'},indent=2))
