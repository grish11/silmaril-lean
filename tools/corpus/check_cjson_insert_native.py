"""Actual loaded ELF observations only; no C provenance or refinement proof."""
import ctypes as C
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
p=ROOT/'corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1'
r=json.loads(p.with_name('receipt.json').read_text());record=next(x for x in r['outputs'] if x['path']==str(p.relative_to(ROOT)))
assert hashlib.sha256(p.read_bytes()).hexdigest()==record['sha256']
class Node(C.Structure):pass
P=C.POINTER(Node)
Node._fields_=[('next',P),('prev',P),('child',P),('type',C.c_int),('valuestring',C.c_char_p),('valueint',C.c_int),('valuedouble',C.c_double),('string',C.c_char_p)]
assert C.sizeof(Node)==64 and [Node.next.offset,Node.prev.offset,Node.child.offset]==[0,8,16]
lib=C.CDLL(str(p));f=lib.cJSON_InsertItemInArray;f.argtypes=[P,C.c_int,P];f.restype=C.c_int
class Info(C.Structure):_fields_=[('name',C.c_char_p),('base',C.c_void_p),('symbol',C.c_char_p),('symbol_address',C.c_void_p)]
dl=C.CDLL(None);dl.dladdr.argtypes=[C.c_void_p,C.POINTER(Info)];dl.dladdr.restype=C.c_int;i=Info()
assert dl.dladdr(C.cast(f,C.c_void_p),C.byref(i)) and C.cast(f,C.c_void_p).value==i.base+24266
assert C.string_at(C.cast(f,C.c_void_p),226)==p.read_bytes()[24266:24266+226]
for seed in range(8):
 for which in [1,3]:
  nodes=[Node() for _ in range(6)];addresses=[C.addressof(n) for n in nodes]
  for k,n in enumerate(nodes):
   raw=bytes((seed+k+j)%256 for j in range(64));C.memmove(C.addressof(n),raw,64)
  root,first,middle,tail,new,unrelated=nodes
  new.next=P()
  root.child=C.pointer(first);first.next=C.pointer(middle);first.prev=C.pointer(tail)
  middle.next=C.pointer(tail);middle.prev=C.pointer(first);tail.next=P();tail.prev=C.pointer(middle)
  before=[C.string_at(C.addressof(n),64) for n in nodes];expected=[bytearray(b) for b in before]
  updates=[(4,0,addresses[2]),(4,8,addresses[1]),(2,8,addresses[4]),(1,0,addresses[4])] if which==1 else [(3,0,addresses[4]),(4,8,addresses[3]),(1,8,addresses[4])]
  for object_index,offset,address in updates:expected[object_index][offset:offset+8]=address.to_bytes(8,'little')
  assert f(C.pointer(root),which,C.pointer(new))==1
  after=[C.string_at(C.addressof(n),64) for n in nodes]
  assert after==[bytes(b) for b in expected]
  wrong=[bytearray(b) for b in expected];wrong[5][32]^=1
  assert after!=[bytes(b) for b in wrong]
  assert after!=before
print(json.dumps({'scope':'finite loaded-native observations, not source/ABI/refinement proof or a registered context','artifact_sha256':record['sha256'],'function_address':24266,'function_size':226,'cases':16,'domain':'six disjoint native64-byte objects, interior index1 / append index3, fresh new.next=null, arbitrary sampled payload bytes','exact_pointer_updates':{'interior':4,'append':3},'unrelated_bytes_preserved':True,'unchanged_heap_and_unrelated_mutation_comparison_negatives':True}))
