; ModuleID = './examples/test6.mlg'
source_filename = "./examples/test6.mlg"

declare {}* @print_int(i64)

define {}* @print_int.13(i64) {
  %2 = call {}* @print_int(i64 %0)
  ret {}* %2
}

define i64 @id.12(i64) {
  ret i64 %0
}

define i32 @main() {
  %1 = call i64 @id.12(i64 42)
  %2 = call i64 @id.12(i64 %1)
  %3 = add i64 %2, 42
  %4 = call i64 @id.12(i64 42)
  %5 = add i64 %3, %4
  %6 = call {}* @print_int.13(i64 %5)
  ret i32 0
}