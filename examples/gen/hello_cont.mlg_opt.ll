; ModuleID = './examples/gen/hello_cont.mlg.ll'
source_filename = "./examples/hello_cont.mlg"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@"$globle_str_44" = unnamed_addr constant [13 x i8] c"hello, world\00"

declare i8* @GC_malloc(i64) local_unnamed_addr

define {}* @"$fo32"(i8* nocapture readonly, {}*) {
  %3 = bitcast {}* %1 to i8*
  %4 = bitcast i8* %0 to i8* (i8*, i8*)**
  %5 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %4, align 8
  %6 = getelementptr i8, i8* %0, i64 8
  %7 = bitcast i8* %6 to i8**
  %8 = load i8*, i8** %7, align 8
  %9 = tail call i8* %5(i8* %8, i8* %3)
  %10 = tail call i8* @GC_malloc(i64 0)
  %11 = bitcast i8* %10 to {}*
  ret {}* %11
}

define {}* @println_k1(i8*, { {}* (i8*, {}*)*, i8* }* nocapture readonly) local_unnamed_addr {
  %3 = tail call {}* @println(i8* %0)
  %4 = getelementptr { {}* (i8*, {}*)*, i8* }, { {}* (i8*, {}*)*, i8* }* %1, i64 0, i32 0
  %5 = load {}* (i8*, {}*)*, {}* (i8*, {}*)** %4, align 8
  %6 = getelementptr { {}* (i8*, {}*)*, i8* }, { {}* (i8*, {}*)*, i8* }* %1, i64 0, i32 1
  %7 = load i8*, i8** %6, align 8
  %8 = tail call {}* %5(i8* %7, {}* %3)
  ret {}* %8
}

declare {}* @println(i8*) local_unnamed_addr

define {}* @println0(i8*) local_unnamed_addr {
  %2 = tail call {}* @println(i8* %0)
  ret {}* %2
}

define i8* @id4(i8*, i8* readnone returned) {
  %3 = tail call i8* @GC_malloc(i64 16)
  %4 = bitcast i8* %3 to i8* (i8*, i8*)**
  store i8* (i8*, i8*)* @id4, i8* (i8*, i8*)** %4, align 8
  %5 = getelementptr i8, i8* %3, i64 8
  %6 = bitcast i8* %5 to i8**
  store i8* %0, i8** %6, align 8
  ret i8* %1
}

declare void @GC_init() local_unnamed_addr

define i32 @main() local_unnamed_addr {
  tail call void @GC_init()
  %1 = tail call i8* @GC_malloc(i64 0)
  %2 = tail call i8* @GC_malloc(i64 16)
  %3 = bitcast i8* %2 to i8* (i8*, i8*)**
  store i8* (i8*, i8*)* @id4, i8* (i8*, i8*)** %3, align 8
  %4 = getelementptr i8, i8* %2, i64 8
  %5 = bitcast i8* %4 to i8**
  store i8* %1, i8** %5, align 8
  %6 = tail call i8* @GC_malloc(i64 16)
  %7 = bitcast i8* %6 to {}* (i8*, {}*)**
  store {}* (i8*, {}*)* @"$fo32", {}* (i8*, {}*)** %7, align 8
  %8 = getelementptr i8, i8* %6, i64 8
  %9 = bitcast i8* %8 to i8**
  store i8* %2, i8** %9, align 8
  %10 = tail call {}* @println(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @"$globle_str_44", i64 0, i64 0))
  %11 = load {}* (i8*, {}*)*, {}* (i8*, {}*)** %7, align 8
  %12 = load i8*, i8** %9, align 8
  %13 = tail call {}* %11(i8* %12, {}* %10)
  ret i32 0
}