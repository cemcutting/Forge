#lang forge

sig A { f : set A }

run {} for {
    #A = 3
    f is tree
}
