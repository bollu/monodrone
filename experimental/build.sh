#!/usr/bin/env sh
set -o xtrace
set -e
cc -g $(leanc --print-cflags) $(leanc --print-ldflags) -L../.lake/build/lib/ ../.lake/build/lib/libMonodroneFat.a ffi.c -o a.out

