# write(1, response, 40); exit(0): one fixed HTTP/1.1 response on stdout.
# The return value of write is ignored, so a short write delivers a prefix.
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $response, %esi  # be imm32         absolute address of the bytes
    mov $40, %edx        # ba 28 00 00 00   length 40
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $0, %edi         # bf 00 00 00 00   status 0
    syscall              # 0f 05
response:
    .ascii "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok"
