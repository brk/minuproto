#!/usr/bin/env python

import sys
import fileinput
import re

# Simple heuristic parser for encoded cap'n'proto uncompressed
# encoded messages, hexdump'ed in format:
#                           (7 hex digit offset)  (xx ){8}
# piped to stdin.
#
# Known Shortcomings
# ==================
# * Will get confused with reverse pointers.
# * Doesn't handle inter-segment pointers.
# * List data is not properly marked,
#   which results in bogus parse failures

def main():
    n = 0

    for line in fileinput.input():
        if line.startswith('+++') or line.startswith('---') or line.startswith('@@'):
            print line,
            continue

        n = n + 1

        m = re.match(r".?([0-9a-f]{7}) ((?: [0-9a-f]{2})+)", line)
        try:
          offset_bytes = int(m.group(1), 16)
          offset_words = offset_bytes / 8

          bytes = m.group(2).strip().split(' ')

          if n == 1:
              print line,
          else:
              print line.rstrip(), interpretations_of(offset_words, bytes)
        except:
          print line,

dataof = {}
ptrsof = {}

def interpretations_of(off_words, bytes_arr):
    interps = []
    # for example, [ 0f 00 00 12 ]
    # corresponds to 0x1200000f
    bytes_chars = ''.join(reversed(bytes_arr))

    def rev(s):
        return s[::-1]

    # stored MSB-to-LSB, as conventionally written
    bitsM = ''.join(bits_of_hexdigit_char(c) for c in bytes_chars)
    print 'M->' + bitsM + '<-L',

    # parses n bits starting o from the MSB
    def iM(o, n):
        return int(bitsM[o:o+n], 2)

    assert len(bitsM) == 64
    # parses n bits starting o from the LSB
    def iL(o, n):
        return iM(64 - (o + n), n)

    def bitsL(o, n):
        x = 64 - (o + n)
        return bitsM[x:x+n]

    def fmttgt(off_w):
        return "%07x" % (off_w * 8)

    if off_words in dataof:
        interps.append('data of ' + dataof[off_words])
        return interps

    if off_words in ptrsof:
        interps.append('ptr of ' + ptrsof[off_words])

    if likely_ascii(bytes_arr):
      interps.append("ascii: " + ''.join([chr(int(x, 16)) for x in bytes_arr]))

    if iL(0,2) == 1:
        offset = iL(2,30)
        target = "%07x" % ((off_words + offset + 1)*8)
        if offset > -123 and offset < 16234:
            interps.append( {'type':'listptr', 'off':offset, 'tgt':target,
                            'tag':bitsM[29:29+3], 'nelts':iM(0, 29) } )
        else:
          if not likely_ascii(bytes_arr):
            interps.append("list ptr, but offset seems bogus")
            interps.append("ascii: " + ''.join([chr(int(x, 16)) for x in bytes_arr]))

    if iL(0,2) == 0:
        offset = iL(2,30)
        target = off_words + offset + 1
        datasz = iL(32,16)
        ptrsiz = iL(48,16)
        for x in range(target, target+datasz):
            dataof[x] = fmttgt(off_words)
        for x in range(target+datasz, target+datasz+ptrsiz):
            ptrsof[x] = fmttgt(off_words)

        if offset > -123 and offset < 16770:
            interps.append( {'type':'structptr', 'off':offset, 'tgt':fmttgt(target),
                            'datsz': datasz, 'ptrsz': ptrsiz
                            } )
        else:
          if not likely_ascii(bytes_arr):
            interps.append("struct ptr, but offset seems bogus")
            interps.append("ascii: " + ''.join([chr(int(x, 16)) for x in bytes_arr]))
    return interps

def likely_ascii(bytes):
  #too_many_zeros = count_zeros(bytes) >= len(bytes)/2
  too_many_zeros = count_zeros(bytes) >= len(bytes)-2
  return all(likely_ascii_char(x) for x in bytes) and not too_many_zeros

def count_zeros(strs):
  return sum(1 if x == '00' else 0 for x in strs)

def likely_ascii_char(s):
  x = int(s, 16)
  return x == 0 or (x > 20 and x < 120)

def bits_of_hexdigit_char(d):
    return {
        '0':'0000',
        '1':'0001',
        '2':'0010',
        '3':'0011',
        '4':'0100',
        '5':'0101',
        '6':'0110',
        '7':'0111',
        '8':'1000',
        '9':'1001',
        'a':'1010',
        'b':'1011',
        'c':'1100',
        'd':'1101',
        'e':'1110',
        'f':'1111',
    }[d]

if __name__ == '__main__':
    main()
