; ModuleID = './examples/polyfun.mlg'
source_filename = "./examples/polyfun.mlg"

define i64 @f147(i8*, i64) {
  %3 = bitcast i8* %0 to { i8* (i8*, i8*)*, i8* }*
  %4 = inttoptr i64 %1 to i8*
  %5 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %3, i32 0, i32 0
  %6 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %5
  %7 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %3, i32 0, i32 1
  %8 = load i8*, i8** %7
  %9 = call i8* %6(i8* %8, i8* %4)
  %10 = ptrtoint i8* %9 to i64
  ret i64 %10
}

define i8* @fw128(i8*, i8*) {
  %3 = bitcast i8* %0 to { i8* (i8*, i8*)*, i8* }*
  %4 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %3, i32 0, i32 0
  %5 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %4
  %6 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %3, i32 0, i32 1
  %7 = load i8*, i8** %6
  %8 = call i8* %5(i8* %7, i8* %1)
  ret i8* %8
}

declare i8* @GC_malloc(i64)

define i32 @main56() {
  %1 = call i8* @GC_malloc(i64 0)
  %2 = bitcast i8* %1 to {}*
  %3 = bitcast {}* %2 to i8*
  %4 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %5 = bitcast i8* %4 to { i8* (i8*, i8*)*, i8* }*
  %6 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 0
  store i8* (i8*, i8*)* @id61, i8* (i8*, i8*)** %6
  %7 = call i8* @GC_malloc(i64 0)
  %8 = bitcast i8* %7 to {}*
  %9 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 1
  store i8* %3, i8** %9
  %10 = call i8* @GC_malloc(i64 0)
  %11 = bitcast i8* %10 to {}*
  %12 = call i8* @GC_malloc(i64 0)
  %13 = bitcast i8* %12 to {}*
  %14 = bitcast {}* %13 to i8*
  %15 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %16 = bitcast i8* %15 to { i64 (i8*, i64)*, i8* }*
  %17 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %16, i32 0, i32 0
  store i64 (i8*, i64)* @addOne60, i64 (i8*, i64)** %17
  %18 = call i8* @GC_malloc(i64 0)
  %19 = bitcast i8* %18 to {}*
  %20 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %16, i32 0, i32 1
  store i8* %14, i8** %20
  %21 = call i8* @GC_malloc(i64 0)
  %22 = bitcast i8* %21 to {}*
  %23 = mul i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), 1
  %24 = call i8* @GC_malloc(i64 %23)
  %25 = bitcast i8* %24 to { i64 (i8*, i64)*, i8* }**
  %26 = alloca i64
  store i64 0, i64* %26
  br label %cond_0

cond_0:                                           ; preds = %copyelem_0, %0
  %27 = load i64, i64* %26
  %28 = icmp slt i64 %27, 1
  br i1 %28, label %copyelem_0, label %end_0

copyelem_0:                                       ; preds = %cond_0
  %29 = getelementptr { i64 (i8*, i64)*, i8* }*, { i64 (i8*, i64)*, i8* }** %25, i64 %27
  store { i64 (i8*, i64)*, i8* }* %16, { i64 (i8*, i64)*, i8* }** %29
  %30 = add i64 %27, 1
  store i64 %30, i64* %26
  br label %cond_0

end_0:                                            ; preds = %cond_0
  %31 = call i8* @GC_malloc(i64 0)
  %32 = bitcast i8* %31 to {}*
  %33 = bitcast {}* %32 to i8*
  %34 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %35 = bitcast i8* %34 to { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }*
  %36 = getelementptr { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }, { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }* %35, i32 0, i32 0
  store { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)* @"$lambda58", { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)** %36
  %37 = call i8* @GC_malloc(i64 0)
  %38 = bitcast i8* %37 to {}*
  %39 = getelementptr { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }, { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }* %35, i32 0, i32 1
  store i8* %33, i8** %39
  %40 = call i8* @GC_malloc(i64 0)
  %41 = bitcast i8* %40 to {}*
  %42 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 0
  %43 = load i8* (i8*, i8*)*, i8* (i8*, i8*)** %42
  %44 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 1
  %45 = load i8*, i8** %44
  %46 = bitcast { i8* (i8*, i8*)*, i8* }* %5 to i8*
  %47 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %48 = bitcast i8* %47 to { i8* (i8*, i8*)*, i8* }*
  %49 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %48, i32 0, i32 0
  store i8* (i8*, i8*)* @fw128, i8* (i8*, i8*)** %49
  %50 = call i8* @GC_malloc(i64 0)
  %51 = bitcast i8* %50 to {}*
  %52 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %48, i32 0, i32 1
  store i8* %46, i8** %52
  %53 = call i8* @GC_malloc(i64 0)
  %54 = bitcast i8* %53 to {}*
  %55 = bitcast { i8* (i8*, i8*)*, i8* }* %48 to i8*
  %56 = call i8* %43(i8* %45, i8* %55)
  %57 = getelementptr { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }, { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }* %35, i32 0, i32 0
  %58 = load { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)** %57
  %59 = getelementptr { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }, { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }* %35, i32 0, i32 1
  %60 = load i8*, i8** %59
  %61 = inttoptr i64 1 to i8*
  %62 = call { { i8*, i8** }* (i8*, i8*)*, i8* }* %58(i8* %60, i8* %61)
  %63 = bitcast { i8* (i8*, i8*)*, i8* }* %5 to i8*
  %64 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %65 = bitcast i8* %64 to { i64 (i8*, i64)*, i8* }*
  %66 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %65, i32 0, i32 0
  store i64 (i8*, i64)* @f147, i64 (i8*, i64)** %66
  %67 = call i8* @GC_malloc(i64 0)
  %68 = bitcast i8* %67 to {}*
  %69 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %65, i32 0, i32 1
  store i8* %63, i8** %69
  %70 = call i8* @GC_malloc(i64 0)
  %71 = bitcast i8* %70 to {}*
  %72 = getelementptr { i64 (i8*, i64)*, i8* }*, { i64 (i8*, i64)*, i8* }** %25, i64 0
  store { i64 (i8*, i64)*, i8* }* %65, { i64 (i8*, i64)*, i8* }** %72
  %73 = call i8* @GC_malloc(i64 0)
  %74 = bitcast i8* %73 to {}*
  %75 = getelementptr { i64 (i8*, i64)*, i8* }*, { i64 (i8*, i64)*, i8* }** %25, i64 0
  %76 = load { i64 (i8*, i64)*, i8* }*, { i64 (i8*, i64)*, i8* }** %75
  %77 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %76, i32 0, i32 0
  %78 = load i64 (i8*, i64)*, i64 (i8*, i64)** %77
  %79 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %76, i32 0, i32 1
  %80 = load i8*, i8** %79
  %81 = call i64 %78(i8* %80, i64 1)
  %82 = call {}* @print_int57(i64 %81)
  ret i32 0
}

declare {}* @print_int(i64)

define {}* @print_int57(i64) {
  %2 = call {}* @print_int(i64 %0)
  ret {}* %2
}

define { { i8*, i8** }* (i8*, i8*)*, i8* }* @"$lambda58"(i8*, i8*) {
  %3 = bitcast i8* %0 to {}*
  %4 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %5 = bitcast i8* %4 to { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }*
  %6 = getelementptr { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }, { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }* %5, i32 0, i32 0
  store { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)* @"$lambda58", { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)** %6
  %7 = call i8* @GC_malloc(i64 0)
  %8 = bitcast i8* %7 to {}*
  %9 = getelementptr { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }, { { { i8*, i8** }* (i8*, i8*)*, i8* }* (i8*, i8*)*, i8* }* %5, i32 0, i32 1
  store i8* %0, i8** %9
  %10 = call i8* @GC_malloc(i64 0)
  %11 = bitcast i8* %10 to {}*
  %12 = call i8* @GC_malloc(i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64))
  %13 = bitcast i8* %12 to { i8* }*
  %14 = getelementptr { i8* }, { i8* }* %13, i32 0, i32 0
  store i8* %1, i8** %14
  %15 = call i8* @GC_malloc(i64 0)
  %16 = bitcast i8* %15 to {}*
  %17 = bitcast { i8* }* %13 to i8*
  %18 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %19 = bitcast i8* %18 to { { i8*, i8** }* (i8*, i8*)*, i8* }*
  %20 = getelementptr { { i8*, i8** }* (i8*, i8*)*, i8* }, { { i8*, i8** }* (i8*, i8*)*, i8* }* %19, i32 0, i32 0
  store { i8*, i8** }* (i8*, i8*)* @"$lambda59", { i8*, i8** }* (i8*, i8*)** %20
  %21 = call i8* @GC_malloc(i64 0)
  %22 = bitcast i8* %21 to {}*
  %23 = getelementptr { { i8*, i8** }* (i8*, i8*)*, i8* }, { { i8*, i8** }* (i8*, i8*)*, i8* }* %19, i32 0, i32 1
  store i8* %17, i8** %23
  %24 = call i8* @GC_malloc(i64 0)
  %25 = bitcast i8* %24 to {}*
  ret { { i8*, i8** }* (i8*, i8*)*, i8* }* %19
}

define { i8*, i8** }* @"$lambda59"(i8*, i8*) {
  %3 = bitcast i8* %0 to { i8* }*
  %4 = getelementptr { i8* }, { i8* }* %3, i32 0, i32 0
  %5 = load i8*, i8** %4
  %6 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %7 = bitcast i8* %6 to { { i8*, i8** }* (i8*, i8*)*, i8* }*
  %8 = getelementptr { { i8*, i8** }* (i8*, i8*)*, i8* }, { { i8*, i8** }* (i8*, i8*)*, i8* }* %7, i32 0, i32 0
  store { i8*, i8** }* (i8*, i8*)* @"$lambda59", { i8*, i8** }* (i8*, i8*)** %8
  %9 = call i8* @GC_malloc(i64 0)
  %10 = bitcast i8* %9 to {}*
  %11 = getelementptr { { i8*, i8** }* (i8*, i8*)*, i8* }, { { i8*, i8** }* (i8*, i8*)*, i8* }* %7, i32 0, i32 1
  store i8* %0, i8** %11
  %12 = call i8* @GC_malloc(i64 0)
  %13 = bitcast i8* %12 to {}*
  %14 = mul i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), 1
  %15 = call i8* @GC_malloc(i64 %14)
  %16 = bitcast i8* %15 to i8**
  %17 = alloca i64
  store i64 0, i64* %17
  br label %cond_0

cond_0:                                           ; preds = %copyelem_0, %2
  %18 = load i64, i64* %17
  %19 = icmp slt i64 %18, 1
  br i1 %19, label %copyelem_0, label %end_0

copyelem_0:                                       ; preds = %cond_0
  %20 = getelementptr i8*, i8** %16, i64 %18
  store i8* %1, i8** %20
  %21 = add i64 %18, 1
  store i64 %21, i64* %17
  br label %cond_0

end_0:                                            ; preds = %cond_0
  %22 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %23 = bitcast i8* %22 to { i8*, i8** }*
  %24 = getelementptr { i8*, i8** }, { i8*, i8** }* %23, i32 0, i32 0
  store i8* %5, i8** %24
  %25 = call i8* @GC_malloc(i64 0)
  %26 = bitcast i8* %25 to {}*
  %27 = getelementptr { i8*, i8** }, { i8*, i8** }* %23, i32 0, i32 1
  store i8** %16, i8*** %27
  %28 = call i8* @GC_malloc(i64 0)
  %29 = bitcast i8* %28 to {}*
  ret { i8*, i8** }* %23
}

define i64 @addOne60(i8*, i64) {
  %3 = bitcast i8* %0 to {}*
  %4 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %5 = bitcast i8* %4 to { i8* (i8*, i8*)*, i8* }*
  %6 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 0
  store i8* (i8*, i8*)* @id61, i8* (i8*, i8*)** %6
  %7 = call i8* @GC_malloc(i64 0)
  %8 = bitcast i8* %7 to {}*
  %9 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 1
  store i8* %0, i8** %9
  %10 = call i8* @GC_malloc(i64 0)
  %11 = bitcast i8* %10 to {}*
  %12 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %13 = bitcast i8* %12 to { i64 (i8*, i64)*, i8* }*
  %14 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %13, i32 0, i32 0
  store i64 (i8*, i64)* @addOne60, i64 (i8*, i64)** %14
  %15 = call i8* @GC_malloc(i64 0)
  %16 = bitcast i8* %15 to {}*
  %17 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %13, i32 0, i32 1
  store i8* %0, i8** %17
  %18 = call i8* @GC_malloc(i64 0)
  %19 = bitcast i8* %18 to {}*
  %20 = add i64 %1, 1
  ret i64 %20
}

define i8* @id61(i8*, i8*) {
  %3 = bitcast i8* %0 to {}*
  %4 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %5 = bitcast i8* %4 to { i8* (i8*, i8*)*, i8* }*
  %6 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 0
  store i8* (i8*, i8*)* @id61, i8* (i8*, i8*)** %6
  %7 = call i8* @GC_malloc(i64 0)
  %8 = bitcast i8* %7 to {}*
  %9 = getelementptr { i8* (i8*, i8*)*, i8* }, { i8* (i8*, i8*)*, i8* }* %5, i32 0, i32 1
  store i8* %0, i8** %9
  %10 = call i8* @GC_malloc(i64 0)
  %11 = bitcast i8* %10 to {}*
  %12 = call i8* @GC_malloc(i64 mul nuw (i64 ptrtoint (i1** getelementptr (i1*, i1** null, i32 1) to i64), i64 2))
  %13 = bitcast i8* %12 to { i64 (i8*, i64)*, i8* }*
  %14 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %13, i32 0, i32 0
  store i64 (i8*, i64)* @addOne60, i64 (i8*, i64)** %14
  %15 = call i8* @GC_malloc(i64 0)
  %16 = bitcast i8* %15 to {}*
  %17 = getelementptr { i64 (i8*, i64)*, i8* }, { i64 (i8*, i64)*, i8* }* %13, i32 0, i32 1
  store i8* %0, i8** %17
  %18 = call i8* @GC_malloc(i64 0)
  %19 = bitcast i8* %18 to {}*
  ret i8* %1
}

define i32 @main() {
  %1 = call i32 @main56()
  ret i32 0
}