#!/bin/sh

/usr/share/ant/bin/ant compile
for f in test/*.c; do
    echo "========================="
    echo "-------------------------"
    echo "Generating code for $f"
    echo "-------------------------"

    java -cp "bin/cls:tools/commons-lang3-3.7.jar:tools/commons-text-1.2.jar:tools/antlr-4.13.1-complete.jar:$CLASSPATH" fr.n7.stl.minic.Driver "$f"

    if [ $? -ne 0 ]; then
        echo "Test $f failed to compile"
        exit 1
    fi

    echo "-------------------------"
    echo "Running code for $f"
    echo "-------------------------"

    java -jar ./runtam.jar test/$(basename "$f" .c).tam > test/$(basename "$f" .c).new_out

    diff -u test/$(basename "$f" .c).out test/$(basename "$f" .c).new_out
    if [ $? -ne 0 ]; then
        echo "Test $f failed to run"
        exit 1
    fi
    rm test/$(basename "$f" .c).new_out
done


for f in test_no_code/*.c; do
    echo "========================="
    echo "-------------------------"
    echo "Type checking $f"
    echo "-------------------------"

    java -cp "bin/cls:tools/commons-lang3-3.7.jar:tools/commons-text-1.2.jar:tools/antlr-4.13.1-complete.jar:$CLASSPATH" fr.n7.stl.minic.Driver "$f"

    if [ $? -ne 0 ]; then
        echo "Test $f failed to compile"
        exit 1
    fi
done
