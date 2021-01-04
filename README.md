# KaGaMi

[![Kagami CI](https://github.com/takoeight0821/kagami/workflows/Kagami%20CI/badge.svg)](https://github.com/takoeight0821/kagami/actions?query=workflow%3A%22Kagami+CI%22)

Kagami is a collection of toy programming language implementaions and toolchain.

## Requirement

* [stack](https://docs.haskellstack.org/en/stable/README/)
* [bdwgc](http://www.hboehm.info/gc/)
* [clang](https://clang.llvm.org/)

## Installation

```sh
$ git clone https://github.com/takoeight0821/kagami
$ cd kagami
$ stack install
```

## Usage

```sh
$ malgoc examples/malgo/hello.mlg -o hello.ll
$ clang hello.ll runtime/malgo/rts.c -lgc
$ ./a.out
Hello, world

$ griffc examples/griff/Hello.grf -o Hello.ll
$ clang Hello.ll runtime/griff/rts.c -lgc
$ ./a.out
Hello, world
```

## Koriel

Some utilities for Kagami and the implementation of the Core internal representation.

## Malgo

A simple functional programming language inspired by MinCaml and Tiger.

## Griff

A functional programming language.
Its syntax is based on Haskell.

### Primitives

```
data Int32 = Int32# Int32#
data Int64 = Int64# Int64#

add_i32# :: (Int32#, Int32#) -> Int32#
add_i64# :: (Int64#, Int64#) -> Int64#
```
