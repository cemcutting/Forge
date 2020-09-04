#lang forge

sig A { f : set B }
sig B { }

run {} for {
    #A = 2
    #B = 2
    f is pbij
}
