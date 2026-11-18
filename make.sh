#!/bin/sh

set -eu

cd "$(dirname "$0")"
rm -rf out

javac -d out module-info.java hol/kernel/*.java hol/lib/*.java hol/syntax/*.java hol/test/*.java
java -p out -m hol/hol.test.Tests
java -p out -m hol/hol.test.Props
