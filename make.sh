#!/bin/sh

set -eu

cd "$(dirname "$0")"
rm -rf out

javac -d out hol/kernel/*.java hol/lib/*.java hol/test/*.java
java -cp out hol.test.Tests
