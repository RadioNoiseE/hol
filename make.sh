#!/bin/sh

set -eu

cd "$(dirname "$0")"

build() {
    rm -rf out
    javac -d out $(find . -name '*.java' -not -path './out/*' -not -path './dist/*')
}

image() {
    build
    jar --create --file hol.jar -C out .
}

shell() {
    image
    jshell --module-path hol.jar --add-modules hol
}

clean() {
    rm -rf out hol.jar
}

case "${1:-build}" in
    build) build;;
    image) image;;
    shell) shell;;
    clean) clean;;
    *)
        echo "usage: $0 [build | image | shell | clean]" >&2
        exit 2
        ;;
esac
