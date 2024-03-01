enqueue:
	@ args = 0, pretend = 0, frame = 16
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #16
	mov	r3, r0
	ldrb	r2, [r3, #96]
	str	r2, [fp, #-20]
	ldr	r0, [r3, #120]
	mov	r1, #804
	mul	r2, r1, r0
	ldr	r1, .L8
	add	r2, r2, r1
	add	r2, r2, #4
	str	r2, [fp, #-16]
	ldr	r0, [r3, #120]
	mov	r1, #804
	mul	r2, r1, r0
	add	r2, r2, #400
	ldr	r1, .L8
	add	r2, r2, r1
	add	r2, r2, #4
	str	r2, [fp, #-12]
	ldr	r2, [fp, #-20]
	lsl	r2, r2, #2
	ldr	r1, [fp, #-16]
	add	r2, r1, r2
	ldr	r2, [r2]
	cmp	r2, #0
	bne	.L4
	ldr	r2, [fp, #-20]
	lsl	r2, r2, #2
	ldr	r1, [fp, #-12]
	add	r2, r1, r2
	str	r3, [r2]
	ldr	r1, [fp, #-20]
	lsl	r1, r1, #2
	ldr	r0, [fp, #-16]
	add	r1, r0, r1
	ldr	r2, [r2]
	str	r2, [r1]
	mov	r2, #0
	str	r2, [r3, #232]
	b	.L5
.L4:
	ldr	r2, [fp, #-20]
	lsl	r2, r2, #2
	ldr	r1, [fp, #-12]
	add	r2, r1, r2
	ldr	r2, [r2]
	str	r3, [r2, #232]
	ldr	r2, [fp, #-20]
	lsl	r2, r2, #2
	ldr	r1, [fp, #-12]
	add	r2, r1, r2
	str	r3, [r2]
	mov	r2, #0
	str	r2, [r3, #232]
.L5:
	ldr	r2, [r3, #120]
	ldr	r3, .L8+4
	ldr	r3, [r3]
	cmp	r2, r3
	bne	.L6
	ldr	r3, .L8+4
	ldr	r0, [r3]
	ldr	r2, .L8
	mov	r1, #804
	mul	r3, r1, r0
	add	r3, r2, r3
	ldr	r3, [r3]
	str	r3, [fp, #-8]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L6
	ldr	r3, .L8+8
	mov	r2, #47
	ldr	r1, .L8+12
	ldr	r0, .L8+16
	bl	__assert_fail
.L6:
	ldr	r3, .L8+4
	ldr	r0, [r3]
	ldr	r2, .L8
	mov	r1, #804
	mul	r3, r1, r0
	add	r3, r2, r3
	ldr	r3, [r3]
	add	r3, r3, #128
	mov	r0, r3
	bl	read_tsc_64
	nop
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L9:
	.align	2
.L8:
	.word	__cpu_local_vars
	.word	cpuid
	.word	__PRETTY_FUNCTION__.5012
	.word	.LC0
	.word	.LC1
