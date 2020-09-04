#lang forge

sig A { f : set B }
sig B { g : set A }

run {} for {
    #A = 2
    #B = 2
    f is bij
    g is bij
}
