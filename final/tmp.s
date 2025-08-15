IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $48, %rsp
	.data
L1:	.string "You must give 2 integers.\n"
	.text
	leaq L1(%rip), %rdi
	movq $0, %rax
	callq printf
	.data
L2:	.string "First integer(base): "
	.text
	leaq L2(%rip), %rdi
	movq $0, %rax
	callq printf
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq %rax, %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq scanf
	.data
L3:	.string "Second integer(exponent): "
	.text
	leaq L3(%rip), %rdi
	movq $0, %rax
	callq printf
	movq %rbp, %rax
	leaq -16(%rax), %rax
	movq %rax, %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq scanf
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	movq %rbp, %rax
	leaq -16(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq %rsi
	popq %rdi
	movq $1, %rax
L4:
	cmpq $0, %rsi
	jle L5
	imulq %rdi, %rax
	subq $1, %rsi
	jmp L4
L5:
	pushq %rax
	movq %rbp, %rax
	leaq -24(%rax), %rax
	popq (%rax)
	.data
L6:	.string "Answer = "
	.text
	leaq L6(%rip), %rdi
	movq $0, %rax
	callq printf
	movq %rbp, %rax
	leaq -24(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq  %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq printf
	.data
L7:	.string "\n"
	.text
	leaq L7(%rip), %rdi
	movq $0, %rax
	callq printf
	leaveq
	retq
