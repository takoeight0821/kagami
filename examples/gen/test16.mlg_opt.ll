; ModuleID = './examples/gen/test16.mlg.ll'
source_filename = "./examples/test16.mlg"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define i64 @fo84(i8* nocapture readonly, i64) {
  %3 = inttoptr i64 %1 to i8*
  %4 = bitcast i8* %0 to i8* (i8*, i8*)**
  %5 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %4, align 8
  %6 = getelementptr i8, i8* %0, i64 8
  %7 = bitcast i8* %6 to i8**
  %8 = load i8*, i8** %7, align 8
  %9 = tail call i8* %5(i8* %8, i8* %3)
  %10 = ptrtoint i8* %9 to i64
  ret i64 %10
}

define i8* @fo71(i8* nocapture readonly, i8*) {
  %3 = bitcast i8* %0 to i8* (i8*, i8*)**
  %4 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %3, align 8
  %5 = getelementptr i8, i8* %0, i64 8
  %6 = bitcast i8* %5 to i8**
  %7 = load i8*, i8** %6, align 8
  %8 = tail call i8* %4(i8* %7, i8* %1)
  ret i8* %8
}

define i8* @fo59(i8* nocapture readonly, i8*) {
  %3 = bitcast i8* %0 to i8* (i8*, i8*)**
  %4 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %3, align 8
  %5 = getelementptr i8, i8* %0, i64 8
  %6 = bitcast i8* %5 to i8**
  %7 = load i8*, i8** %6, align 8
  %8 = tail call i8* %4(i8* %7, i8* %1)
  ret i8* %8
}

declare i8* @GC_malloc(i64) local_unnamed_addr

define i8* @id28(i8*, i8* readnone returned) {
  %3 = tail call i8* @GC_malloc(i64 16)
  %4 = bitcast i8* %3 to i8* (i8*, i8*)**
  store i8* (i8*, i8*)* @id28, i8* (i8*, i8*)** %4, align 8
  %5 = tail call i8* @GC_malloc(i64 0)
  %6 = getelementptr i8, i8* %3, i64 8
  %7 = bitcast i8* %6 to i8**
  store i8* %0, i8** %7, align 8
  %8 = tail call i8* @GC_malloc(i64 0)
  ret i8* %1
}

declare {}* @print_int(i64) local_unnamed_addr

define {}* @print_int27(i64) local_unnamed_addr {
  %2 = tail call {}* @print_int(i64 %0)
  ret {}* %2
}

define i32 @main() local_unnamed_addr {
  %1 = tail call i8* @GC_malloc(i64 0)
  %2 = tail call i8* @GC_malloc(i64 16)
  %3 = bitcast i8* %2 to i8* (i8*, i8*)**
  store i8* (i8*, i8*)* @id28, i8* (i8*, i8*)** %3, align 8
  %4 = tail call i8* @GC_malloc(i64 0)
  %5 = getelementptr i8, i8* %2, i64 8
  %6 = bitcast i8* %5 to i8**
  store i8* %1, i8** %6, align 8
  %7 = tail call i8* @GC_malloc(i64 0)
  %8 = tail call i8* @GC_malloc(i64 16)
  %9 = bitcast i8* %8 to i8**
  store i8* %2, i8** %9, align 8
  %10 = tail call i8* @GC_malloc(i64 0)
  %11 = getelementptr i8, i8* %8, i64 8
  %12 = bitcast i8* %11 to i8**
  store i8* %2, i8** %12, align 8
  %13 = tail call i8* @GC_malloc(i64 0)
  %14 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %3, align 8
  %15 = load i8*, i8** %6, align 8
  %16 = tail call i8* @GC_malloc(i64 16)
  %17 = bitcast i8* %8 to i64*
  %18 = load i64, i64* %17, align 8
  %19 = bitcast i8* %16 to i64*
  store i64 %18, i64* %19, align 8
  %20 = tail call i8* @GC_malloc(i64 0)
  %21 = load i64, i64* %17, align 8
  %22 = getelementptr i8, i8* %16, i64 8
  %23 = bitcast i8* %22 to i64*
  store i64 %21, i64* %23, align 8
  %24 = tail call i8* @GC_malloc(i64 0)
  %25 = tail call i8* %14(i8* %15, i8* %16)
  %26 = tail call i8* @GC_malloc(i64 16)
  %27 = bitcast i8* %25 to i64*
  %28 = load i64, i64* %27, align 8
  %29 = tail call i8* @GC_malloc(i64 16)
  %30 = bitcast i8* %29 to i8* (i8*, i8*)**
  store i8* (i8*, i8*)* @fo59, i8* (i8*, i8*)** %30, align 8
  %31 = tail call i8* @GC_malloc(i64 0)
  %32 = getelementptr i8, i8* %29, i64 8
  %33 = bitcast i8* %32 to i64*
  store i64 %28, i64* %33, align 8
  %34 = tail call i8* @GC_malloc(i64 0)
  %35 = bitcast i8* %26 to i8**
  store i8* %29, i8** %35, align 8
  %36 = tail call i8* @GC_malloc(i64 0)
  %37 = load i64, i64* %27, align 8
  %38 = tail call i8* @GC_malloc(i64 16)
  %39 = bitcast i8* %38 to i8* (i8*, i8*)**
  store i8* (i8*, i8*)* @fo71, i8* (i8*, i8*)** %39, align 8
  %40 = tail call i8* @GC_malloc(i64 0)
  %41 = getelementptr i8, i8* %38, i64 8
  %42 = bitcast i8* %41 to i64*
  store i64 %37, i64* %42, align 8
  %43 = tail call i8* @GC_malloc(i64 0)
  %44 = getelementptr i8, i8* %26, i64 8
  %45 = bitcast i8* %44 to i8**
  store i8* %38, i8** %45, align 8
  %46 = tail call i8* @GC_malloc(i64 0)
  %47 = bitcast i8* %26 to i64*
  %48 = load i64, i64* %47, align 8
  %49 = tail call i8* @GC_malloc(i64 16)
  %50 = bitcast i8* %49 to i64 (i8*, i64)**
  store i64 (i8*, i64)* @fo84, i64 (i8*, i64)** %50, align 8
  %51 = tail call i8* @GC_malloc(i64 0)
  %52 = getelementptr i8, i8* %49, i64 8
  %53 = bitcast i8* %52 to i8**
  %54 = bitcast i8* %52 to i64*
  store i64 %48, i64* %54, align 8
  %55 = tail call i8* @GC_malloc(i64 0)
  %56 = load i64 (i8*, i64)*, i64 (i8*, i64)** %50, align 8
  %57 = load i8*, i8** %53, align 8
  %58 = tail call i64 %56(i8* %57, i64 1)
  %59 = tail call {}* @print_int(i64 %58)
  ret i32 0
}