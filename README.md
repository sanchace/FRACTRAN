This is an implementation of FRACTRAN in Lean 4, with the goal of
exploring computable functions.

# About

## FRACTRAN
[FRACTRAN](https://en.wikipedia.org/wiki/FRACTRAN) was [introduced in
the 1980's](https://www.cs.cmu.edu/~cdm/resources/Conway87.pdf) by
*the legendary* [John
H. Conway](https://en.wikipedia.org/wiki/John_Horton_Conway).  Its
**programs** are defined by lists of rational numbers, and its
**states** are simply interpreted as integers.  The transition from a
state to the next is determined by multiplication by the first
rational in the list which results in an integer.  Therefore,
FRACTRAN's semantics is beautifully transparent and at a
psychologically very comfortable level of abstraction.  Moreover,
FRACTRAN encodes a simple universal program, making it of theoretical
interest.

## Lean 4
[Lean 4](https://lean-lang.org/) is a hybrid *interactive theorem
prover* and more-or-less *fully-fledged general-purpose functional
programming language*.  That makes it an ideal candidate for studying
a foundational language like FRACTRAN.  In this repository, we both
write more-or-less runable FRACTRAN code and prove theorems about its
behavior.

## Special notes about our implementation
In the spirit of Lean's theorem proving style/conventions, we diverge
from the original presentation of FRACTRAN in two ways:
1. We use integers to represent states instead of naturals; this makes
   some typing marginally cleaner.
2. We represent runs as infinite sequences and use a halting state,
   represented by zero.

# Getting started

## Installing Lean 4

### Microsoft Inc.
As Lean is developed by Microsoft Research, [all available
documentation](https://lean-lang.org/lean4/doc/quickstart.html) will
suggest using [Visual Studio Code](https://code.visualstudio.com/) as
an editor with a fairly tightly integrated development environment via
the Lean 4 language server protocol.  With that said, it is also
possible to use Lean 4 with Emacs if you're willing to go off the
beaten path.

### Elan, Lake, Lean, and LSP
- If you've already installed VS Code and you want to do things the
easy way, simply follow [this
guide](https://lean-lang.org/lean4/doc/quickstart.html) to install
everything the easy way.
- *Alternatively*, *make sure you have [Git
  installed](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)
  on your system* and try your luck at following [these
  instructions](https://lean-lang.org/lean4/doc/setup.html) to install
  **elan** onto your system, and then following [these
  instructions](https://lean-lang.org/lean4/doc/setup.html#setting-up-lean)
  to install and properly configure **Lean 4** and **Lake**.  If you
  choose not to use VS Code, then you'll also want to install the Lean
  4 Language Server Protocol (LSP) at this point for your chosen
  editor; for Emacs, this is doable by following [these
  instructions](https://lean-lang.org/lean4/doc/setup.html#setting-up-lean).
  
### Installing this *Lean 4 Project*
If you just try cloning this repo (like a regular person might)
without doing *any of the extra steps*, then you might have a bad
time.  Make sure to follow [these
instructions](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git),
with this project substituted for `mathematics in lean` (which is a
great resource for leaning Lean!).

## Leaning Lean 4
### Natural Numbers Game
If you've made it this far (or even if you haven't), try playing [the
natural numbers
game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).  This
should give you all the background you need to start poking around in
this project.

### Mathematics in Lean
There is also [Mathematics in
Lean](https://leanprover-community.github.io/mathematics_in_lean/), a
fairly complete introduction to Lean.  This has everything you'll
practically need for this project, and much much more.

### Mathlib Documentation
The official code documentation for mathlib can be found
[here](https://leanprover-community.github.io/mathlib4_docs/).  You'll
want to [see `Nat` in
`Init.Prelude`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Nat),
as well as [`Rat` in
`Std.Data.Rat.Basic`](https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat),
and [`List` in
`Init.Prelude`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#List).
Also helpful are the files in `Mathlib.Tactic`, e.g., [convert](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#List).

It is also worth mentioning that most of the structures we import from
`Init` and `Std` have analogous definitions `Mathlib` which are
typically downstream.  We might switch to importing exclusively from
`Mathlib` in the future.
