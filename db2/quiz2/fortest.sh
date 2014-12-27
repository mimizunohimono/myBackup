#!/bin/sh
arg=100
while [ $arg -ne 1000 ]
do
arg=`expr $arg + 100`

./gen.exe ${arg}
echo "hash-join test"
./hash-join
echo "hash-bnlj test"
./hash-bnlj
done
