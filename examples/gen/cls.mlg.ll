; ModuleID = './examples/cls.mlg'
source_filename = "./examples/cls.mlg"

define i32 @main19() {
  %1 = call { i64 (i8*, i64)*, i8* }* @add20(i64 3)
  %2 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %1, i32 0, i32 0
  %3 = load i64 (i8*, i64)*, i64 (i8*, i64)** %2
  %4 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %1, i32 0, i32 1
  %5 = load i8*, i8** %4
  %6 = call i64 %3(i8* %5, i64 4)
  ret i32 0
}

declare i8* @GC_malloc(i64)

define { i64 (i8*, i64)*, i8* }* @add20(i64) {
  %2 = call i8* @GC_malloc(i64 ptrtoint (i64* getelementptr (i64, i64* null, i32 1) to i64))
  %3 = bitcast i8* %2 to { i64 }*
  %4 = getelementptr { i64 }, { i64 }* %3, i32 0, i32 0
  store i64 %0, i64* %4
  %5 = call i8* @GC_malloc(i64 0)
  %6 = bitcast i8* %5 to {}*
  %7 = bitcast { i64 }* %3 to i8*
  %8 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %9 = bitcast i8* %8 to { i64 (i8*, i64)*, i8* }*
  %10 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %9, i32 0, i32 0
  store i64 (i8*, i64)* @add_inner21, i64 (i8*, i64)** %10
  %11 = call i8* @GC_malloc(i64 0)
  %12 = bitcast i8* %11 to {}*
  %13 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %9, i32 0, i32 1
  store i8* %7, i8** %13
  %14 = call i8* @GC_malloc(i64 0)
  %15 = bitcast i8* %14 to {}*
  ret { i64 (i8*, i64)*, i8* }* %9
}

define i64 @add_inner21(i8*, i64) {
  %3 = bitcast i8* %0 to { i64 }*
  %4 = getelementptr { i64 }, { i64 }* %3, i32 0, i32 0
  %5 = load i64, i64* %4
  %6 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %7 = bitcast i8* %6 to { i64 (i8*, i64)*, i8* }*
  %8 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %7, i32 0, i32 0
  store i64 (i8*, i64)* @add_inner21, i64 (i8*, i64)** %8
  %9 = call i8* @GC_malloc(i64 0)
  %10 = bitcast i8* %9 to {}*
  %11 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %7, i32 0, i32 1
  store i8* %0, i8** %11
  %12 = call i8* @GC_malloc(i64 0)
  %13 = bitcast i8* %12 to {}*
  %14 = add i64 %5, %1
  ret i64 %14
}

define i32 @main() {
  %1 = call i32 @main19()
  ret i32 0
}
