#! /bin/sh
for i in *sva; do
    sleep 2
    cat $i
    cargo run -- --print-mir --print-llir -o test.o -O $i || continue
    cc test.o -o test || continue
    rm test.o
    echo
    echo === RUNNING ===
    echo
    ./test
    echo $?
done
