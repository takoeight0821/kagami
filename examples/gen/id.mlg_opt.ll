; ModuleID = './examples/gen/id.mlg.ll'
source_filename = "./examples/id.mlg"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: norecurse nounwind readnone
define i64 @id.5(i64 returned) local_unnamed_addr #0 {
  ret i64 %0
}

; Function Attrs: norecurse nounwind readnone
define i32 @main() local_unnamed_addr #0 {
  ret i32 0
}

attributes #0 = { norecurse nounwind readnone }