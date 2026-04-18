import VersoSlides
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open VersoSlides

#doc (Slides) "My Presentation" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
width := some 1920
%%%

# Chapter 2

This is a presentation built with
[`verso-slides`](https://github.com/leanprover/verso-slides).

# Table of Contents
  + Simple Proofs using `rw`
  + Identities in Algebraic Structures
  + `apply`-ing Theorems and Lemmas (and how to find them)
  + Proofs in Algebraic Structures
-- + Bonus: What happened? (What do `apply` and `rw` actually do?)
  + Bonus: Tactics that make this (mostly) obsolete

# First Goal

```lean

example (a b c : ℝ) :
    a * b * c = b * (a * c) := by
  sorry
```

# Theorems available to us:

```lean
#check mul_comm
```

`#check` command gives us the type of an expression

# Theorems available to us:

```lean
#check mul_comm
```
  - `u_1`: Universe metavariable: not important for know
  - `{G : Type}`: for any type `G`
  - `[CommMagma G]`: with a commutative operation `*` on `G`
  - `(a b : G)`: for any `a` and `b` of type `G`
  - `a * b = b * a` is true

# Theorems available to us:

```lean
#check mul_comm
```
=> For any type with a commutative operation  `*`, we know that `a * b = b * a` holds for any `a` and `b`.

:::fragment currentlyVisible
Curry Howard: `mul_comm` is a function that takes a type `G` with a commutative operation `*` and two variables `a` and `b` of type `G`as an input and returns a term of type `a * b = b * a`.
:::

# Theorems available to us:

```lean
#check mul_comm
#check mul_assoc
```

Multiplication in `ℝ` commutative and a semigroup, so the two theorems can be applied with `G := ℝ`.

# Goal

```lean

example (a b c : ℝ) :
    a * b * c = b * (a * c) := by
  sorry
```

Note: Multiplication in lean is left associative, so `a * b * c = (a * b) * c`
(can also be seen when hovering in VSCode).


# Goal

```lean
example (a b c : ℝ) :
    a * b * c = b * (a * c) := by
  sorry
```
Steps on Paper: `a * b * c = b * a * c = b * (a * c)`

# Goal

```lean
example (a b c : ℝ) :
    a * b * c = b * (a * c) := by
-- !fragment
  rw [mul_comm a b]
-- ^ !click
-- !fragment
  rw [mul_assoc b a c]
```

# Goal

```lean
example (a b c : ℝ) :
    a * b * c = b * (a * c) := by
  rw [mul_comm a b]
-- ^ !click
-- !fragment
  exact mul_assoc b a c

/- !hide-/
section
/- !end hide-/

variable (a b c : ℝ)

#check mul_assoc b a c
/- !hide -/
end
/- !end hide-/
```

# Facts from the local context

```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
   a * (b * e) = c * (d * f) := by
-- !fragment
  rw [h']
-- ^ !click
-- !fragment
  rw [← mul_assoc]
  -- "←" rewrites backwards
  rw [h]
  rw [mul_assoc]
```
:::fragment
Note: The `rw` tactic matches the first occurence of a pattern (for example the left side of `mul_assoc`) when no explicit variables are given.
:::

# Rewrites can be grouped together
```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
    a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
```

# Slightly longer Proofs

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
```

+ Quite difficult to figure out what is going on.

# Calc-Proofs

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    -- !fragment
    _ = a * a + b * a + (a * b + b * b) := by
    -- !fragment
      rw [mul_add, add_mul, add_mul]
    -- !fragment
    _ = a * a + (b * a + a * b) + b * b := by
    -- !fragment
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
```

+ Proof structure is much clearer

# Calc-Proofs with tactics
```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    _ = a * a + b * a + (a * b + b * b) := by
      grind
    _ = a * a + (b * a + a * b) + b * b := by
      ring
    _ = a * a + 2 * (a * b) + b * b := by
      group
```


+ Smaller goals are easier for automation Tactics
+ (caveat: in this case, the entire goal can be solved by grind in one shot)

# Rewriting *inside* local assumptions

```lean
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
    c = 2 * a * d := by
-- !fragment
  rw [hyp'] at hyp
-- !fragment
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
```

# Proving identities in algebraic Structures

```lean
/- !hide -/
section
/- !end hide -/
variable (M : Type*) [Monoid M]
/- !hide -/
end
/- !end hide -/

```
+ `M` is an arbitrary Type
+ which has to have a `Monoid` instance... (What does this mean?)

# Typeclasses

```lean
/- !hide -/
section
/- !end hide -/
class MySemigroup (G : Type*) where
  mul : G → G → G
  mul_assoc (a b c : G) : mul (mul a b) c = mul a (mul b c)

-- !fragment
instance : MySemigroup ℕ where
  mul a b := a * b
  mul_assoc a b c := by rw [mul_assoc]

#synth MySemigroup ℕ

-- !fragment
#synth Ring ℝ
/- !hide -/
end
/- !end hide -/
```

+ Typeclasses can give types additional Properties
+ `[Ring α]` ensures that `α` has an instance of `Ring`
+ `#synth Ring ℝ` can be used to check if a typeclass exists on a given type

# Ring Axioms

```lean

/- !hide -/
section
/- !end hide -/
variable (R : Type*) [Ring R]

#check @add_assoc R _
#check @add_comm R _
#check @zero_add R _
#check @neg_add_cancel R _
#check @mul_assoc R _
#check @mul_one R _
#check @one_mul R _
#check @mul_add R _
#check @add_mul R _
/- !hide -/
end
/- !end hide -/
```

# Ring

```lean
/- !hide -/
section
/- !end hide -/
variable {R : Type*}[Ring R]
/- !hide -/
end
/- !end hide -/
```
+ When we prove something about this arbitrary Ring `R`, it holds in any type with a `Ring` instance (for example `ℝ`, `ℚ` or `ℂ`)

# Sections and Namespaces

```lean
/- !hide -/
section
/- !end hide -/

variable (x y : ℝ → Prop)

section Test

variable (a : ℝ) (h : a = 3.14)

#where

end Test

#where

/- !hide -/
end
/- !end hide -/
```

# Sections and Namespaces
```lean
namespace Test

def hello := "Hello World"

end Test

#eval Test.hello

/-- error: Unknown identifier `hello` -/
#guard_msgs in
#eval hello

open Test

#eval hello
```

# Ring

```lean
namespace MyRing

variable {R : Type*}[Ring R]
```
- New namespace allows us to reprove mathlib theorems about Rings

# Implicit Arugments

```lean -panel

theorem add_left_cancel' (a b c : R) (h : a + b = a + c) : b = c := by sorry
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by sorry

variable (a b c : R) (h : a + b = a + c)
#check add_left_cancel' a b c h
#check add_left_cancel h
--
-- !fragment
#check @add_left_cancel
#check @add_left_cancel R _ a b c h
```
+ *Curly Brackets* mark implicit arguments that can be determined from the context
+ *Round Brackets* mark explicit arguments that have to be provided every time
+ `@` makes all arguments explicit

# Introducing new goals
We can use `add_left_cancel` to show that `a * 0 = 0` follows from the ring axioms:

```lean
theorem mul_zero (a : R) : a * 0 = 0 := by
-- !fragment
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    -- !fragment
    rw [← mul_add, add_zero, add_zero]
-- !fragment
  rw [add_left_cancel h]
/- !hide -/
end MyRing
/- !end hide -/
```
+ The *`have`* Tactic introduces a new goal, which can be used as a local assumption later

# Definitional Equality

In every Ring, substraction is *provably equal* to the addition of the additive inverse:
```lean
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
```

# Definitional Equality

In the real numbers, subtraction is *defined* as the addition of the additive inverse:
```lean
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
```
+ The `rfl` tactic tells lean to unfold both sides of the definition
+ It can complete a proof if both sides are *definitionally equal*

# Example of Definitional Equality

```lean
example : 3 + 4 = 7 := rfl

example : 23 * 2 = 46 := rfl

```

# Preorder

Naive way:
```lean
namespace v1

class MyPreorder (α : Type*) where
  le : α → α → Prop
  le_refl (a : α) : le a a
  le_trans (a b c : α) : le a b → le b c → le a c

end v1
```
:::fragment
- Hard to read without the `≤` syntax
:::

# Preorder

```lean
/- !hide -/
namespace myLe
/- !end hide -/
class MyLE (α : Type*) where
  le : α → α → Prop

scoped infixl:100 " ≤ " => MyLE.le

class MyPreorder (α : Type*) extends MyLE α where
  le_refl (a : α) : a ≤ a
  le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c

instance (α β : Type*) [instPreorder : MyPreorder β] : MyPreorder (α → β) where
  le f g := ∀ a : α, f a ≤ g a
  le_refl f a := instPreorder.le_refl (f a)
  le_trans f1 f2 f3 h1 h2 a := by
    apply instPreorder.le_trans _ (f2 a) _
    · apply h1
    · exact h2 a
/- !hide -/
end myLe
/- !end hide -/
```




# Preorder in Mathlib
```
class Preorder (α : Type u_2) extends LE α, LT α : Type u_2
A preorder is a reflexive, transitive relation ≤....
    le : α → α → Prop
    lt : α → α → Prop
    le_refl (a : α) : a ≤ a
    le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c
    lt_iff_le_not_ge (a b : α) : a < b ↔ a ≤ b ∧ ¬b ≤ a
Instances...
```
:::notes
Who notices anything different from my previous definition?
:::
:::fragment
+ Why are there fields for `lt` and `lt_iff_le_not_ge`? (They seem redundant)
:::

# Preorder in Mathlib
```lean
/--
A preorder is a reflexive, transitive relation `≤`.
In a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by default.
You can override this definition to set a better def-eq.
-/
class Preorder' (α : Type*) extends LE α, LT α where
  protected le_refl : ∀ a : α, a ≤ a
  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl
```
:::fragment
+ `lt` and `lt_iff_le_not_ge` have default values
+ They can be overwritten for better definitional equalities (example: Lexicographical Ordering)
:::


# Using Theorems and Lemmas

```lean
#check le_trans

-- !fragment
/- !hide -/
section
variable {α : Type*} [Preorder α] (a b c: α)
/- !end hide -/
variable (h : a ≤ b) (h' : b ≤ c)

#check @le_trans α _
#check le_trans h
#check le_trans h h'
/- !hide-/
end
/- !end hide-/
```

# The `apply` tactic

takes a proof term and tries to match it to the current goal. The missing hypotheses are left as new goals.

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁
```

# The `apply` tactic


```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁
```

# The `apply` tactic

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀ h₁
```

# The `apply` tactic

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  exact le_trans h₀ h₁
```

# The `apply` tactic

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁
```

# Rewriting with Equivalences

```lean
/- !hide -/
open Real
variable (a b : ℝ) (h : a ≤ b)
/- !end hide -/
example (h : a ≤ b) : rexp a ≤ rexp b := by
  rw [exp_le_exp]
  exact h

#check @exp_le_exp a b
```
+ `rw` can also rewrite along *bi-implications* (if-and-only-if)

TODO irgendwo kurze zusammenfassung dazwischen

# Bi-implications

Bi-implications can be used as normal implications by using `.mp` (modus ponens) and `.mpr` (modus ponens reverse)

```lean
#check exp_le_exp.mpr
#check exp_le_exp.mpr h
example (h : a ≤ b) : rexp a ≤ rexp b :=
  exp_le_exp.mpr h

```
(This proof is only possible because we know `exp_le_exp` exists)

# Strategies to find Mathlib Theorems

+ Guess the name (together with `ctrl + click`)


# Examples of Mathlib Naming convention:

+ `(a + b) * c = a * c + b * c`
   `add_mul`
+ `a - b ≤ c - d ↔ a + d ≤ c + b`
   `sub_le_sub_iff`

# Guess the theorem

` (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d`
:::fragment
`add_le_add`
:::

:::fragment
`a * b = 1 ↔ a = 1 ∧ b = 1`
:::

:::fragment
`mul_eq_one`
:::

# Strategies to find Mathlib Theorems

+ Guess the name (together with `ctrl + click`)
+ Search the mathlib documentation:
  `https://leanprover-community.github.io/mathlib4_docs/Mathlib`
+ use *loogle*:
  `https://loogle.lean-lang.org/`
+ use the `apply?`, `exact?`, `rw?` or `rw??` tactics

# Try to find the following theorem in mathlib

- group homomorphism `f : G → H`
- `G/ker f` and `range f` are isomorphic

:::fragment
- Solution: `QuotientGroup.quotientKerEquivRange` (found using leansearch)
:::

# Try to find the following theorem in mathlib


- group homomorphism is injective if and only if it has a trivial kernel
:::fragment
- Solution: `MonoidHom.ker_eq_bot_iff` (found using MathlibDocs)
:::

# Min-Function on the Reals

```lean
/- !hide -/
variable (a b c : ℝ)
/- !end hide -/
#check @min ℝ _
```
- Note: Arrows associate to the right, so: `ℝ → ℝ → ℝ = ℝ → (ℝ → ℝ)`
:::fragment
```lean
#check min a
#check min a b
```
- A function that returns another function is effectively a function with two paramters (this is called _currying_ after Haskell Curry)
:::

:::fragment
- Note: Function application binds tighter than many other operations:

`min a b + c = (min a b) + c`
:::

# Min-Function on the Reals

```lean
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
```
:::fragment
```lean
-- A very useful lemma when dealing with inequalities:
#check @le_antisymm ℝ _
```
:::

# Commutativitiy of Min-Function

```lean
section
example : min a b = min b a := by
-- !fragment
  apply le_antisymm
-- !fragment
  · apply le_min
    · apply min_le_right
    apply min_le_left
-- !fragment
  · apply le_min
    · apply min_le_right
    apply min_le_left
end
```
:::fragment
- This proof is redundant
:::


# Commutativitiy of Min-Function

```lean
section
example : min a b = min b a := by
  have h (x y : ℝ) : min x y ≤ min y x := by
    apply le_min
    · apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
end
```

# Commutativitiy of Min-Function

```lean
section
example : min a b = min b a := by
  have h {x y : ℝ} : min x y ≤ min y x := by
    apply le_min
    · apply min_le_right
    apply min_le_left
  exact le_antisymm h h
end
```



# Divisibility Relation on ℕ

```lean

example {x y z : ℕ} (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁
```

- `x | y` states `y` is divisible by `x`
- Type `\|` to get `∣` (not the same as `|`)
- Refered to as `dvd` in theorem names

# Divisibility Relation on ℕ

```lean
example : Nat.gcd m n = Nat.gcd n m := by
  sorry
```
- Try to guess the theorem name needed to prove this! (hint: similar to Partial Orders)

# Divisibility Relation on ℕ

```lean
example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · sorry -- exercise
  · sorry -- exercise
```

# Partial Orders
```
class PartialOrder (α : Type u_2) extends Preorder α :
Type u_2

A partial order is a reflexive, transitive, antisymmetric relation ≤.

    le : α → α → Prop
    lt : α → α → Prop
    le_refl (a : α) : a ≤ a
    le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c
    lt_iff_le_not_ge (a b : α) : a < b ↔ a ≤ b ∧ ¬b ≤ a
    le_antisymm (a b : α) : a ≤ b → b ≤ a → a = b

Instances...
```

# Lattices

```lean
/- !hide -/
section
/- !end hide-/
variable {α : Type*} [Lattice α]
variable (x y z : α)
#synth PartialOrder α
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
/- !hide -/
end
/- !end hide -/
```

# Supremum and Infimum

- `⊔` _(`\sup`)_ is called: supremum, join or least upper bound (lub)
- `⊓` _(`\inf`)_ is called: infimum, meet or greatest lower bound (glb)

# Instances of Lattices

```lean
#synth Lattice ℤ -- with `min` and `max`

#synth Lattice (Set R) -- with ∪ and ∩
-- Note that this instance is synthesized from a `CompleteLattice` instance.

#synth Lattice Bool -- with ∧ and ∨

variable {α : Type*} [TopologicalSpace α]
#synth Lattice (TopologicalSpace.Opens α)

```

# Tips for proofs in Lattices

```lean
variable {α : Type*} [Lattice α] (a b c : α)

example : a ⊓ b = b ⊓ a := by
  -- it is often easier to prove the two inequalities
  apply le_antisymm
  · sorry
  · sorry

example (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  trans b -- introduces two new goals
  · exact h1
  · exact h2

```

# Summary
+ `rw [h] (at h1)` replaces an occurence of the left side of `h` with the right side of `h`
+ `apply h` matches the goal state with the statement of h and introduces missing assumpations as new goals
+ `exact h` tries to close the goal using `h`
+ `have h (a b : α) : .... := by` introduces a new goal that can later be reused
+ `section` and `namespace` can be used to limit the scope of variables and influence name resolutions
+ `#check` can be used to see the type of an expression
+ `#eval` can be used to evalute an expression

# Useful Tactics

+ `exact?` searches for theorem to close the goal
+ `apply?` searches for theorem that matches the goal state
+ `rw?` searches for possible rewrites
+ `rw??` allows you to shift-click on a part of the theorem to rewrite

# Useful Tactics
You can get information on a tactic in the docstring (hovering in vscode).
+ `simp`: simplifies the goal using all lemmas that are tagged with `@[simp]`
+ `grind`: SMT-Solver, tries to close the goal from existing facts
+ `linarith`: proves linear (in)equalities from assumptions
+ `ring`: Tries to close the goal by using the axioms of a commutative ring
+ Many more in the *tactic-cheatsheet*

# Useful Tactics
+ `simp?` shows what `simp` did
+ `grind?` shows what `grind` did
+ `try?` and `hint` try many tactics and give suggestions to close the goal

# Questions?

# Exercises!


TODO einmal mit strg f nach todo suchen

TODO vlt examples für die tactics
