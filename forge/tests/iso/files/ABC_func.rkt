#lang forge

sig A { 
    f : set B,
    g : set C
}
sig B { h : set A }
sig C { }


run {} for {
    #A = 2
    #B = 2
    #C = 2
    f is func
    g is func
    h is func
}
