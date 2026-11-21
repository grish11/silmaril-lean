# A one-request HTTP/1.1 server on 0.0.0.0:8080/tcp, no libc.
#   socket, bind 8080, listen, accept one connection, send the 40-octet response
#   until all of it is sent (short sends are retried), read once to drain the
#   request, exit 0 (the kernel closes the connection).
# Every failing call before the drain exits with its own status (10..14); sends use
# MSG_NOSIGNAL, so a peer that went away is the error status 14, not SIGPIPE.
    .text
    .globl _start
_start:
    mov $41, %eax          # socket(AF_INET, SOCK_STREAM, 0)
    mov $2, %edi
    mov $1, %esi
    xor %edx, %edx
    syscall
    test %rax, %rax
    js fail_socket
    mov %rax, %rbx         # the listening descriptor
    mov $49, %eax          # bind(fd, &addr, 16)
    mov %rbx, %rdi
    mov $addr, %esi
    mov $16, %edx
    syscall
    test %rax, %rax
    jnz fail_bind
    mov $50, %eax          # listen(fd, 1)
    mov %rbx, %rdi
    mov $1, %esi
    syscall
    test %rax, %rax
    jnz fail_listen
    mov $43, %eax          # accept(fd, NULL, NULL)
    mov %rbx, %rdi
    xor %esi, %esi
    xor %edx, %edx
    syscall
    test %rax, %rax
    js fail_accept
    mov %rax, %r12         # the connection
    mov $response, %esi
    mov $40, %edx
send:
    mov $44, %eax          # sendto(conn, p, n, MSG_NOSIGNAL, NULL, 0)
    mov %r12, %rdi
    mov $0x4000, %r10d
    xor %r8d, %r8d
    xor %r9d, %r9d
    syscall
    test %rax, %rax
    jle fail_send
    add %rax, %rsi         # retry the rest after a short send
    sub %rax, %rdx
    jnz send
    xor %eax, %eax         # read(conn, buf, 1024): drain the request (its result is not used)
    mov %r12, %rdi
    mov $buf, %esi
    mov $1024, %edx
    syscall
    mov $60, %eax          # exit(0); the kernel closes the connection
    xor %edi, %edi
    syscall
fail_socket:
    mov $10, %edi
    jmp fail
fail_bind:
    mov $11, %edi
    jmp fail
fail_listen:
    mov $12, %edi
    jmp fail
fail_accept:
    mov $13, %edi
    jmp fail
fail_send:
    mov $14, %edi
fail:
    mov $60, %eax
    syscall
addr:                      # struct sockaddr_in: AF_INET, port 8080 (big-endian), INADDR_ANY
    .short 2
    .byte 0x1f, 0x90
    .long 0
    .quad 0
response:
    .ascii "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok"
buf:
    .space 1024
