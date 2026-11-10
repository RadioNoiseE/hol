#!/bin/sh

set -eu

cd "$(dirname "$0")"

javac -d out hol/kernel/*.java hol/test/*.java
java -cp out hol.test.Tests
