#!/bin/sh
arg=0
echo "s2pl test"
while [ $arg -ne 10 ]
do
arg=`expr $arg + 10`
./s2pl.exe ${arg}
done
arg=`expr 0`
echo "2pl test"
while [ $arg -ne 10 ]
do
arg=`expr $arg + 10`
./2pl.exe ${arg}
done
