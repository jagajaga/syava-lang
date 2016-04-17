#! /bin/sh
cargo run -- --print-mir --print-llir -o test.o -O src/test.sva || exit
gcc test.o -o test || exit
rm test.o
echo
echo === RUNNING ===
echo
./test
echo $?
