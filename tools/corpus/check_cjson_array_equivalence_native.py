import ctypes as C, hashlib,json,subprocess,re,struct
from pathlib import Path
root=Path(__file__).resolve().parents[2]
paths=['corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1','corpus/elf/cjson/x86_64/libcjson.so.1']
libs=[];records=[]
class Info(C.Structure):
 _fields_=[('name',C.c_char_p),('base',C.c_void_p),('symbol',C.c_char_p),('symbol_address',C.c_void_p)]
dl=C.CDLL(None);dl.dladdr.argtypes=[C.c_void_p,C.POINTER(Info)];dl.dladdr.restype=C.c_int
for path,addr,size in zip(paths,[0x5382,0x4090],[81,35]):
 p=root/path;receipt=json.loads(p.with_name('receipt.json').read_text());record=next(x for x in receipt['outputs'] if x['object']=='libcjson.so.1');assert hashlib.sha256(p.read_bytes()).hexdigest()==record['sha256']
 syms=subprocess.check_output(['readelf','-Ws',str(p)],text=True);assert re.search(rf'{addr:016x}\s+{size}\s+FUNC\s+GLOBAL\s+DEFAULT\s+\d+\s+cJSON_GetArraySize',syms)
 lib=C.CDLL(str(p));f=lib.cJSON_GetArraySize;f.argtypes=[C.c_void_p];f.restype=C.c_int
 info=Info();assert dl.dladdr(C.cast(f,C.c_void_p),C.byref(info));assert C.cast(f,C.c_void_p).value==info.base+addr
 raw=p.read_bytes();ph=struct.unpack_from('<Q',raw,32)[0];ent,count=struct.unpack_from('<HH',raw,54)
 for i in range(count):
  typ,flags,off,va,pa,fs,ms,al=struct.unpack_from('<IIQQQQQQ',raw,ph+i*ent)
  if typ==1 and va<=addr and addr+size<=va+fs:code=raw[off+addr-va:off+addr-va+size];break
 else:raise AssertionError('symbol is unmapped')
 assert C.string_at(C.cast(f,C.c_void_p).value,size)==code
 libs.append((lib,f));records.append(dict(path=path,sha256=record['sha256'],address=addr,size=size,bytes_hex=code.hex()))
assert C.cast(libs[0][1],C.c_void_p).value!=C.cast(libs[1][1],C.c_void_p).value
class Node(C.Structure):
 _fields_=[('next',C.c_void_p),('prev',C.c_void_p),('child',C.c_void_p),('type',C.c_int),('valuestring',C.c_void_p),('valueint',C.c_int),('valuedouble',C.c_double),('string',C.c_void_p)]
assert C.sizeof(Node)==64
assert libs[0][1](None)==libs[1][1](None)
for n in range(65):
 nodes=(Node*(n+1))()
 base=C.addressof(nodes)
 assert base%8==0 and 65536<=base and base+65*64<2**47
 assert all(C.addressof(nodes[j])==base+64*j for j in range(n+1))
 for j,node in enumerate(nodes):C.memmove(C.addressof(node),bytes((j*31+k)%256 for k in range(64)),64)
 nodes[0].child=C.addressof(nodes[1]) if n else None
 for j in range(1,n+1):nodes[j].next=C.addressof(nodes[j+1]) if j<n else None
 before=b''.join(C.string_at(C.addressof(node),64) for node in nodes)
 left=libs[0][1](C.addressof(nodes[0]));assert before==b''.join(C.string_at(C.addressof(node),64) for node in nodes)
 right=libs[1][1](C.addressof(nodes[0]));assert before==b''.join(C.string_at(C.addressof(node),64) for node in nodes)
 assert left==right
print(json.dumps(dict(artifacts=records,cases=66,actual_native_return_equality=True,caller_memory_preserved=True,scope='Finite native pair observations; binary obligation UNPROVED, no semantic proof; finite healthy null/list inputs0..64 only, not general or source-refinement evidence; no artifact rebuilds'),indent=2))
