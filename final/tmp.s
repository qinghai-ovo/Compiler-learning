IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $16, %rsp
	pushq $5
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
	.data
L1:	.string "x = "
	.text
	leaq L1(%rip), %rdi
	movq $0, %rax
	callq printf
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq  %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq printf
	.data
L2:	.string "\n"
	.text
	leaq L2(%rip), %rdi
	movq $0, %rax
	callq printf
	leaveq
	retq
	pushq $5
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
