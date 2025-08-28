; ModuleID = 'obliv_c/obliv_bits.c'
source_filename = "obliv_c/obliv_bits.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx15.0.0"

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %destKnown = alloca i32, align 4
  %destUnknown = alloca i32, align 4
  %copyKnown = alloca i32, align 4
  %copyUnknown = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 0, ptr %destKnown, align 4
  store i32 0, ptr %destUnknown, align 4
  %0 = load i32, ptr %destKnown, align 4
  %1 = load i32, ptr %copyKnown, align 4
  %cmp = icmp ne i32 %0, %1
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %2 = load i32, ptr %destUnknown, align 4
  %3 = load i32, ptr %copyUnknown, align 4
  %cmp1 = icmp ne i32 %2, %3
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  %4 = load i32, ptr %copyKnown, align 4
  store i32 %4, ptr %destKnown, align 4
  %5 = load i32, ptr %copyUnknown, align 4
  store i32 %5, ptr %destUnknown, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %lor.lhs.false
  ret i32 0
}

attributes #0 = { noinline nounwind ssp uwtable(sync) "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+sha3,+v8.1a,+v8.2a,+v8.3a,+v8.4a,+v8.5a,+v8a,+zcm,+zcz" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 1}
!3 = !{i32 7, !"frame-pointer", i32 1}
!4 = !{!"Homebrew clang version 17.0.6"}
