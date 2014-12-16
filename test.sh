#!/bin/bash

# Reads a compiled/serialized cap'n'proto schema file,
# and generates the corresponding code.
runhaskell Main.hs < testdata/test2.schema.bin || exit 1

# Reads a serialized cap'n'proto message and serializes
# it back out, using the above-generated code.
runhaskell Test2.hs || exit 1

# Compare the original and serialized file to make
# sure they are identical.
M1=testdata/test2_0.msg
M2=${M1}.ser

diff ${M1} ${M2}

#dump () { hexdump$1 }

hexdump  -e '"%07.7_ax  "  8/1 "%02x " "\n"' ${M1} > ${M1}.hex.txt
hexdump  -e '"%07.7_ax  "  8/1 "%02x " "\n"' ${M2} > ${M2}.hex.txt

# Note the "reversed" order here, which makes it so that
# our (presumably wrong) file is the color red, indicating brokenness.
diff -s -U 100 ${M2}.hex.txt ${M1}.hex.txt | python explain-capnproto-bytes.py | colordiff | ./third_party/diff-highlight
















#git diff --color=always ${M2}.hex.txt ${M1}.hex.txt | ./third_party/diff-highlight | tail -n +3

