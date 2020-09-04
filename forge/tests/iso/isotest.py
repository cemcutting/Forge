#!/usr/local/bin/python3

"""
This file tests 2 commands for equivalence.
ex: ./isotest.py "racket isoEx.rkt" "racket isoEx.rkt"
"""

########

import os
from subprocess import Popen, PIPE, check_output

########

# FIXME: only run this on trusted forge specs!
# FIXME: lack of sanitization makes this vulnarable to malicious atoms

def forgeW(cmd):
    # TODO: make this interactive with subprocess.Popen
    cmd = f"{cmd} --write"
    for line in check_output(cmd.split()).decode().splitlines():
        if line.startswith("INSTANCE : #hash("):
            line = line[len("INSTANCE : "):]
            yield(line)

def forgeR(cmd, inst):
    cmd = f"{cmd} --read "
    for line in check_output(cmd.split()+[inst]).decode().splitlines():
        if line.startswith("INSTANCE : #hash("):
            return line[len("INSTANCE : "):]
    return False

def isotest(P, Q):
    print(f'Testing: P ≅ Q for P="{P}", Q="{Q}"')
    
    print(f'\tTesting: ∀I(I⊧P => ∃J(J⊧Q and J≅I))')
    for I in forgeW(P):
        print(f'\t\tTesting: I={I}')
        J = forgeR(Q, I)
        if J: print(f'\t\tPassed: J={J}')
        else: 
            print(f'\t\tFailed: No such J')
            return False
    print(f'\tPassed: ∀I(I⊧P => ∃J(J⊧Q and J≅I))')

    print(f'\tTesting: ∀J(J⊧Q => ∃I(I⊧P and I≅J))')
    for J in forgeW(Q):
        print(f'\t\tTesting: J={J}')
        I = forgeR(P, J)
        if I: print(f'\t\tPassed: I={I}')
        else: 
            print(f'\t\tFailed: No such I')
            return False
    print(f'\tPassed: ∀J(J⊧Q => ∃I(I⊧P and I≅J))')

    print(f'Passed: P ≅ Q for P="{P}", Q="{Q}"')
    return True

########

if __name__ == "__main__":
    import sys
    cmd1 = sys.argv[1]
    cmd2 = sys.argv[2]
    isotest(cmd1, cmd2)






