#!/bin/bash

make clean;
mkdir $USER
cp -r Integration manual_reduction minimizer prefixscan Procedures $USER;
cd $USER; find . -not \( -name  "*.c" -or  -name "Makefile" -or -name "*.h" -or -type d \) | xargs rm; cd ..;
tar zcvf $USER.tgz $USER;
rm -rf $USER;
