#!/usr/bin/env bash

TESTDIR=/tmp/griff_test
mkdir $TESTDIR

echo '=== no opt ==='
for file in `ls ./examples/griff`; do
  echo $file;
  cabal exec griffc -- --no-opt ./examples/griff/$file -o $TESTDIR/$file.ll && \
  clang $(pkg-config bdw-gc --libs --cflags) ./runtime/griff/rts.c $TESTDIR/$file.ll -o $TESTDIR/$file.out && \
  $TESTDIR/$file.out || exit 255
  echo 'SUCCESS!!'
done

echo '=== opt ==='
for file in `ls ./examples/griff`; do
  echo $file;
  cabal exec griffc -- ./examples/griff/$file -o $TESTDIR/$file.ll && \
  clang $(pkg-config bdw-gc --libs --cflags) ./runtime/griff/rts.c $TESTDIR/$file.ll -o $TESTDIR/$file.out && \
  $TESTDIR/$file.out || exit 255
  echo 'SUCCESS!!'
done
