define i64 @main () {
  %2 = alloca i64
  store i64 2, i64* %2
  %3 = shl i64 5, %2
  ret i64 %3
}