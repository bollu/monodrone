#!/usr/bin/env sh
set -e
set -o xtrace
clang -Wall -Werror -fsanitize=address -fsanitize=undefined -g main.c $(leanc --print-cflags) $(leanc --print-ldflags) -L../.lake/build/lib/ -lMonodroneFat -o main.out
