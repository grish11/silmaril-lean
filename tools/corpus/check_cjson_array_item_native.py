import ctypes as C, hashlib, json
from pathlib import Path
p=Path(__file__).resolve().parents[2] / 'corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson.so.1'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='0c7ab3d1ba9aa7808bab6e22695e2fee1702753ad0f4570ce53952120629b456'
class Node(C.Structure): pass
Node._fields_=[('next',C.POINTER(Node)),('prev',C.POINTER(Node)),('child',C.POINTER(Node)),('type',C.c_int),('valuestring',C.c_void_p),('valueint',C.c_int),('valuedouble',C.c_double),('string',C.c_void_p)]
assert C.sizeof(Node)==64 and Node.child.offset==16 and Node.next.offset==0
lib=C.CDLL(str(p));f=lib.cJSON_GetArrayItem;f.argtypes=[C.POINTER(Node),C.c_int];f.restype=C.c_void_p
observations=[]
for n in [*range(9),64]:
 for seed in range(3):
  nodes=(Node*(n+2))()
  assert C.addressof(nodes)%8==0 and 1048576<=C.addressof(nodes) and C.addressof(nodes)+66*64<2**47
  if n: nodes[0].child=C.pointer(nodes[1])
  for i in range(1,n):nodes[i].next=C.pointer(nodes[i+1])
  for i in range(n+2):nodes[i].type=0x123400+i+seed;nodes[i].valueint=100+i+seed
  before=C.string_at(C.addressof(nodes),C.sizeof(nodes))
  for is_null in [False,True]:
   for index in [-1,0,1,4,8,9,2147483647]:
    result=f(None if is_null else C.pointer(nodes[0]),index)
    expected=None if is_null or index<0 or index>=n else C.addressof(nodes[index+1])
    assert result==expected,(n,index,result,expected)
    assert C.string_at(C.addressof(nodes),C.sizeof(nodes))==before
    observations.append({'length':n,'seed':seed,'null':is_null,'index':index,'return':'null' if result is None else f'node[{index+1}]','caller_and_unrelated_bytes_preserved':True})
print(json.dumps({'status':'finite native audit only; no registered context or semantic proof','artifact_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'cases':observations},indent=2))
