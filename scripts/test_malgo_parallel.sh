#!/usr/bin/env bash

set -eu

TESTDIR=/tmp/malgo_test
mkdir -p $TESTDIR
mkdir -p $TESTDIR/libs

BUILD=cabal

eval "$BUILD exec malgo -- to-ll --force -M $TESTDIR/libs ./runtime/malgo/Builtin.mlg -o $TESTDIR/libs/Builtin.ll"
eval "$BUILD exec malgo -- to-ll --force -M $TESTDIR/libs ./runtime/malgo/Prelude.mlg -o $TESTDIR/libs/Prelude.ll"
cp ./runtime/malgo/rts.c $TESTDIR/libs/rts.c

pids=()

echo '=== no opt no lambdalift ==='

test_nono () {
  LLFILE=$TESTDIR/${file/.mlg/-nono.ll}
  OUTFILE=$TESTDIR/${file/.mlg/.out-nono}

  echo $file

  cat ./examples/malgo/$file | grep -q '^-- Expected: '

  eval "$BUILD exec malgo -- to-ll --force --no-opt --no-lambdalift -M $TESTDIR/libs ./examples/malgo/$file -o $LLFILE"

  clang -Wno-override-module $(pkg-config bdw-gc --libs --cflags) $TESTDIR/libs/rts.c $TESTDIR/libs/Prelude.ll $TESTDIR/libs/Builtin.ll $LLFILE -o $OUTFILE

  test "$($OUTFILE)" = "$(cat ./examples/malgo/$file | grep '^-- Expected: ' | sed -e 's/^-- Expected: //')"
}

for file in `ls ./examples/malgo | grep '\.mlg$'`; do
  test_nono &
  pids+=($!)
done

for pid in "${pids[@]}"; do
  wait "$pid"
done
pids=()

echo '=== no opt ==='

test_noopt () {
  LLFILE=$TESTDIR/${file/.mlg/-noopt.ll}
  OUTFILE=$TESTDIR/${file/.mlg/.out-noopt}

  echo $file

  cat ./examples/malgo/$file | grep -q '^-- Expected: '

  eval "$BUILD exec malgo -- to-ll --force --no-opt -M $TESTDIR/libs ./examples/malgo/$file -o $LLFILE"

  clang -Wno-override-module $(pkg-config bdw-gc --libs --cflags) $TESTDIR/libs/rts.c $TESTDIR/libs/Prelude.ll $TESTDIR/libs/Builtin.ll $LLFILE -o $OUTFILE

  test "$($OUTFILE)" = "$(cat ./examples/malgo/$file | grep '^-- Expected: ' | sed -e 's/^-- Expected: //')"
}

for file in `ls ./examples/malgo | grep '\.mlg$'`; do
  test_noopt &
  pids+=($!)
done

for pid in "${pids[@]}"; do
  wait "$pid"
done
pids=()

echo '=== no lambdalift ==='

test_nolift () {
  LLFILE=$TESTDIR/${file/.mlg/-nolift.ll}
  OUTFILE=$TESTDIR/${file/.mlg/.out-nolift}

  echo $file

  cat ./examples/malgo/$file | grep -q '^-- Expected: '

  eval "$BUILD exec malgo -- to-ll --force --no-lambdalift -M $TESTDIR/libs ./examples/malgo/$file -o $LLFILE"

  clang -Wno-override-module $(pkg-config bdw-gc --libs --cflags) $TESTDIR/libs/rts.c $TESTDIR/libs/Prelude.ll $TESTDIR/libs/Builtin.ll $LLFILE -o $OUTFILE

  test "$($OUTFILE)" = "$(cat ./examples/malgo/$file | grep '^-- Expected: ' | sed -e 's/^-- Expected: //')"
}

for file in `ls ./examples/malgo | grep '\.mlg$'`; do
  test_nolift &
  pids+=($!)
done

for pid in "${pids[@]}"; do
  wait "$pid"
done
pids=()

echo '=== opt ==='

test_opt () {
  LLFILE=$TESTDIR/${file/.mlg/-opt.ll}
  OUTFILE=$TESTDIR/${file/.mlg/.out}

  echo $file

  cat ./examples/malgo/$file | grep -q '^-- Expected: '

  eval "$BUILD exec malgo -- to-ll --force -M $TESTDIR/libs ./examples/malgo/$file -o $LLFILE"

  clang -Wno-override-module $(pkg-config bdw-gc --libs --cflags) $TESTDIR/libs/rts.c $TESTDIR/libs/Prelude.ll $TESTDIR/libs/Builtin.ll $LLFILE -o $OUTFILE

  test "$($OUTFILE)" = "$(cat ./examples/malgo/$file | grep '^-- Expected: ' | sed -e 's/^-- Expected: //')"
}

for file in `ls ./examples/malgo | grep '\.mlg$'`; do
  test_opt &
  pids+=($!)
done

for pid in "${pids[@]}"; do
  wait "$pid"
done