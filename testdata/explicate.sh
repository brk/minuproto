#!/bin/sh

# Usage:
#   explicate.sh foo
#
# Will generate:
#
#   foo.schema.bin
#   foo.schema.txt
#
# from foo.capnp

capnp compile -o./dump.sh ${1}.capnp -I./capnp
mv out.schema.bin ${1}.schema.bin
< ${1}.schema.bin capnp decode schema.capnp CodeGeneratorRequest > ${1}.schema.txt
