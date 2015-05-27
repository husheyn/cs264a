#!/bin/bash

OUTPUT_FOLDER="test_result"
TEST_FILES=./benchmarks/sampled/*
TIMEOUT="5s"

rm -f $OUTPUT_FOLDER/*.out
rmdir -f $OUTPUT_FOLDER
mkdir $OUTPUT_FOLDER
(cd primitives/ && make clean)
(cd primitives/ && make)
cp primitives/libsat.a c2D_code/lib/darwin/
(cd c2D_code/ && make clean)
(cd c2D_code/ && make)

for f in $TEST_FILES
do
	filename="$(basename "$f")"
	echo "Testing $filename file..."
	gtimeout $TIMEOUT executables/c2D/darwin/c2D -c $f -W > $OUTPUT_FOLDER/$filename.out
	gtimeout $TIMEOUT c2D_code/bin/darwin/c2D -c $f -W > $OUTPUT_FOLDER/my_$filename.out
done


