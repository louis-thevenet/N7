#!/bin/sh

/usr/share/ant/bin/ant compile

for f in test_fail/*.c; do
    echo "========================="
    echo "-------------------------"
    echo "Testing failing tests $f"
    echo "-------------------------"

    java -cp "bin/cls:tools/commons-lang3-3.7.jar:tools/commons-text-1.2.jar:tools/antlr-4.13.1-complete.jar:$CLASSPATH" fr.n7.stl.minic.Driver "$f"

done
