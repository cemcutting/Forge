#!/usr/local/bin/python3

"""
This file tests a file for equivalence w/ and w/o boundsy breaks.
ex: ./boundsytest.py isoEx.rkt
"""

########

from isotest import *

########

def boundsytest(file):
    cmd1 = f'racket {file}'
    cmd2 = f'racket {file} --boundsy 0'
    return isotest(cmd1, cmd2)

########

if __name__ == "__main__":
    import sys
    file = sys.argv[1]
    boundsytest(file)