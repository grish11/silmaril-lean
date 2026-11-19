"""Bounded ELF data/RELA evidence, separate from function CodeAt or loader claims."""
import hashlib
import struct

def export(data, specs):
    if not isinstance(specs,list) or len(specs)>8:
        raise ValueError('unbounded data bindings')
    if not specs:return []
    if data[:6]!=b'\x7fELF\x02\x01':raise ValueError('expected ELF64LE data binding')
    phoff,shoff=struct.unpack_from('<QQ',data,32)
    phsize,phnum,shsize,shnum=struct.unpack_from('<HHHH',data,54)
    def section(i):
        if not 0<=i<shnum:raise ValueError('invalid data section')
        return struct.unpack_from('<IIQQQQIIQQ',data,shoff+i*shsize)
    def symbol(s,index):
        if s[1] not in (2,11) or s[9]!=24 or not 0<=index<s[5]//24:raise ValueError('invalid data symbol table')
        names=section(s[6]);strings=data[names[4]:names[4]+names[5]]
        n,info,_,_,address,size=struct.unpack_from('<IBBHQQ',data,s[4]+index*24)
        return strings[n:strings.index(0,n)].decode(),info&15,address,size
    def mapped(address,size):
        if not 0<size<=4096:raise ValueError('unbounded data excerpt')
        for j in range(phnum):
            typ,flags,off,va,_,filesz,_,_=struct.unpack_from('<IIQQQQQQ',data,phoff+j*phsize)
            if typ==1 and flags&4 and va<=address and address+size<=va+filesz:
                offset=off+address-va;raw=data[offset:offset+size]
                if len(raw)!=size:raise ValueError('truncated ELF data')
                return offset,raw
        raise ValueError('data outside readable file-backed segment')
    result=[]
    for spec in specs:
        expected=(spec['symbol'],1,spec['address'],spec['size'])
        if not any(symbol(section(j),k)==expected for j in range(shnum) if section(j)[1] in (2,11) for k in range(section(j)[5]//24)):
            raise ValueError('ELF data symbol identity mismatch')
        offset,raw=mapped(spec['address'],spec['size'])
        if raw.hex(' ')!=spec['bytes_hex']:raise ValueError('ELF data bytes mismatch')
        relocation=spec['relocation'];at=relocation['file_offset']
        tables=[section(j) for j in range(shnum) if section(j)[1]==4 and section(j)[4]<=at and at+24<=section(j)[4]+section(j)[5] and (at-section(j)[4])%24==0]
        if len(tables)!=1 or tables[0][9]!=24:raise ValueError('missing/ambiguous ELF RELA record')
        slot,info,addend=struct.unpack_from('<QQq',data,at)
        if (slot,info>>32,info&0xffffffff,addend)!=(relocation['slot'],relocation['symbol_index'],6,0):
            raise ValueError('GLOB_DAT relocation mismatch')
        if symbol(section(tables[0][6]),info>>32)!=expected:raise ValueError('relocation data symbol mismatch')
        slot_offset,slot_raw=mapped(slot,8)
        if slot_raw.hex(' ')!=relocation['slot_bytes_hex']:raise ValueError('ELF GOT slot bytes mismatch')
        result.append({'symbol':spec['symbol'],'address':spec['address'],'size':len(raw),'file_offset':offset,'bytes_hex':raw.hex(' '),'sha256':hashlib.sha256(raw).hexdigest(),
            'relocation':{'file_offset':at,'size':24,'bytes_hex':data[at:at+24].hex(' '),'slot':slot,'slot_file_offset':slot_offset,'slot_bytes_hex':slot_raw.hex(' '),'symbol_index':info>>32,'type':'R_X86_64_GLOB_DAT','addend':addend},
            'limit':'Actual file data/symbol/relocation evidence only; the context restricts post-loader slot resolution. No dynamic-loader, interposition or source-refinement theorem.'})
    return result
