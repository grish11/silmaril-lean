"""Existing ELF loaded-native observations; not a semantic or loader proof."""
import ctypes as C,hashlib,json,struct,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
p=ROOT/'corpus/elf/sqlite/x86_64/libsqlite3.so';raw=p.read_bytes();address,size=79888,8
receipt=json.loads(p.with_name('receipt.json').read_text());record=next(x for x in receipt['outputs'] if x['object']=='libsqlite3.so');assert hashlib.sha256(raw).hexdigest()==record['sha256']
ph=struct.unpack_from('<Q',raw,32)[0];ent,n=struct.unpack_from('<HH',raw,54)
def excerpt(address,size):
 for j in range(n):
  typ,flags,off,va,pa,fs,ms,al=struct.unpack_from('<IIQQQQQQ',raw,ph+j*ent)
  if typ==1 and va<=address and address+size<=va+fs:return raw[off+address-va:off+address-va+size]
 raise AssertionError('unmapped address')
code=excerpt(address,size);assert code==bytes.fromhex('48 8b 05 b1 b7 0f 00 c3')
got=address+7+int.from_bytes(code[3:7],'little',signed=True);assert got==0x10efc8
relocs=subprocess.check_output(['readelf','-rW',str(p)],text=True);assert '000000000010efc8  000000e900000006 R_X86_64_GLOB_DAT      00000000000ed572 sqlite3_version + 0' in relocs
symbols=subprocess.check_output(['readelf','-Ws',str(p)],text=True);assert '00000000000ed572     7 OBJECT  GLOBAL DEFAULT   14 sqlite3_version' in symbols
assert excerpt(0xed572,7)==b'3.54.1\0'
class Info(C.Structure):_fields_=[('name',C.c_char_p),('base',C.c_void_p),('symbol',C.c_char_p),('symbol_address',C.c_void_p)]
lib=C.CDLL(str(p));f=lib.sqlite3_libversion;f.argtypes=[];f.restype=C.c_void_p
info=Info();dl=C.CDLL(None);dl.dladdr.argtypes=[C.c_void_p,C.POINTER(Info)];dl.dladdr.restype=C.c_int
assert dl.dladdr(C.cast(f,C.c_void_p),C.byref(info));assert C.cast(f,C.c_void_p).value==info.base+address
assert C.string_at(info.base+address,size)==code
array=(C.c_char*7).in_dll(lib,'sqlite3_version');assert C.addressof(array)==info.base+0xed572
assert C.c_void_p.from_address(info.base+got).value==C.addressof(array)
for _ in range(16):assert f()==C.addressof(array) and C.string_at(f(),7)==b'3.54.1\0'
print(json.dumps({'artifact':'corpus/elf/sqlite/x86_64/libsqlite3.so','sha256':record['sha256'],'function':{'symbol':'sqlite3_libversion','address':address,'size':size,'bytes_hex':code.hex(' ')},'global':{'symbol':'sqlite3_version','address':0xed572,'size':7,'bytes_hex':excerpt(0xed572,7).hex(' ')},'got':{'address':got,'relocation':'R_X86_64_GLOB_DAT sqlite3_version +0','actual_native_resolution_to_this_ELF_global':True},'loaded_native_observations':16,'scope':'Local observations; actual post-loader no-interposition resolution inspected; not loader/source refinement or semantic proof'},indent=2))
