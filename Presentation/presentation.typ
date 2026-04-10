// Get Polylux from the official package repository
#import "@preview/polylux:0.4.0": *

// Make the paper dimensions fit for a presentation and the text larger
#set page(paper: "presentation-16-9")
#set text(size: 20pt, font: "JetBrains Mono")

// Use #slide to create a slide and style it using your favourite Typst functions
#slide[
  = Table of Contents
  + Simple Proofs using `rw`
  + Identities in Algebraic Structures
  + `apply`-ing Theorems and Lemmas (and how to find them)
    TODO name guessing game
  + Proofs in Algebraic Structures
  + Bonus: What happened? (What do `apply` and `rw` actually do?)
  + Bonus: Tactics that make this (mostly) obsolete

]

// A simple slide
#slide[
  - Goal:
  ```lean
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  ```
 #uncover(2)[
  - Theorems available to us:
  ```lean
  #check mul_comm -- mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a
  ```
  What does this mean?
 ]
]

#slide[
  ```lean
  #check mul_comm -- mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a
  ```
  - `u_1`: Universe metavariable: not important for know
  - `{G : Type}`: for any type `G`
  - `[CommMagma G]`: with a commutative operation `*` on `G`
  - `(a b : G)`: for any `a` and `b` of type `G`
  - `a * b = b * a` is true

  => For any type with a commutative operation, `a * b = b * a` holds for any `a` and `b`

  #uncover(2)[
  Curry Howard: `mul_comm` is a function that takes a type `G` which has to have a Commutative operation `*` and two elements of `G` as an input and returns a term of type `a * b = b * a`
  ]

]


#slide[
  - Goal:
  ```lean
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  ```
 #uncover(2)[
  - Theorems available to us:
  ```lean
  #check mul_comm --  [CommMagma G] (a b : G) : a * b = b * a
  #check mul_assoc --  [Semigroup G] (a b c : G) : a * b * c = a * (b * c) 
  ```
 ]
=> Multiplication in $RR$ is commutative and a semigroup so these two theorems apply with $G := RR$

]

#slide[
  - Goal:
  ```lean
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  ```
  - Note: Multiplication is normally left associative, so: $a * b * c = (a * b) * c$

]

#slide[
  - Goal:
  ```lean
  a b c : ℝ
⊢ a * b * c = b * (a * c)
  ```
- Steps on Paper: $a * b * c = b * a * c = b * (a * c)$
- in Lean:
  ```lean
  rw [mul_comm a b]
  ```
  substitutes `a * b` with `b * a` and gives us a new goal of:
  ```lean
  a b c : ℝ
⊢ b * a * c = b * (a * c)```  

]

#slide[
  Our Goal is now:
  ```lean
  a b c : ℝ
⊢ b * a * c = b * (a * c)```  
  we can use 
  ```lean
  rw [mul_assoc b a c]```
  to substitute `b * a * c` with `b * (a * c)` which makes the two sides of the goal equal and completes the proof.

  #uncover(2)[
    This goal can also be solved by:
    ```lean
    exact mul_assoc b a c```
    because `m̀ul_assoc b a c` gives us exactly the term that is our current goal.
  ]

  ]

#slide[
`rw` can also use facs from the local context:
#columns(2)[
```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
```
#colbreak()
```
a b c d e f : ℝ
h : a * b = c * d
h' : e = f
⊢ a * (b * e) = c * (d * f)
```
]
gives us
]




