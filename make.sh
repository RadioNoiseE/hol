#!/bin/sh

set -eu

cd "$(dirname "$0")"

javac -d out hol/*.java
java -cp out hol.Tests
