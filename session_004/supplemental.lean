/-
 ____                  _                            _        _
/ ___| _   _ _ __  ___| | ___ _ __ ___   ___ _ __ | |_ __ _| |
\___ \| | | | '_ \/ __| |/ _ \ '_ ` _ \ / _ \ '_ \| __/ _` | |
 ___) | |_| | |_) \__ \ |  __/ | | | | |  __/ | | | || (_| | |
|____/ \__,_| .__/|___/_|\___|_| |_| |_|\___|_| |_|\__\__,_|_|
            |_|
   Q&A: List, induction, and the iota rule
-/

/-
Q1. What does the `cons` in `List.cons` stand for?

`cons` is short for "construct". The name comes from Lisp (1958), where
`cons` was the primitive that built a pair (a "cons cell") from a head and
a tail. Lean inherits the term: `List.cons a l` constructs a new list by
prepending `a` to `l`. The infix `a :: l` is sugar for `List.cons a l`.
-/

#check @List.cons         -- @List.cons : {α : Type u_1} → α → List α → List α
#eval List.cons 0 [1, 2]  -- [0, 1, 2]
#eval 0 :: [1, 2]         -- [0, 1, 2]  -- same call, different notation

/-
Q2. What about `List.nil`?

`nil` comes from Latin *nihil*, meaning "nothing". It is the empty-list
constructor. The bracket notation `[]` is sugar for `List.nil`.

Together, `nil` and `cons` are the *only* two constructors of `List`:
every list is built by zero or more `cons`es ending in a `nil`.
-/

#check @List.nil          -- @List.nil : {α : Type u_1} → List α
example : ([] : List Nat) = List.nil := rfl
example : [1, 2, 3] = 1 :: 2 :: 3 :: ([] : List Nat) := rfl

/-
Q3. So is this the inductive (mathematical) definition of a list, so
    that lists can be used both as a data structure AND for proving
    things in a dependent type theory like Lean's?

Yes. The inductive declaration does three jobs at once.

  (a) It pins down the *data*: a list is either `nil` or `cons a l`.
      No other shapes exist — no nulls, no hidden cases.

  (b) It generates a *recursor* `List.rec` automatically. The recursor
      is simultaneously a recursion principle (for defining functions)
      and an induction principle (for proving ∀-statements over lists).

  (c) It pins down the *computation rules*: applying `List.rec` to a
      concrete constructor reduces in a fixed way (see Q4: ι-rule).

Here is the definition Lean uses (built in, but morally this):
-/

namespace QA
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α
end QA

/-
The auto-generated recursor has roughly this type:

  List.rec :
    {α : Type u} → {motive : List α → Sort v} →
    motive nil →                                                 -- nil case
    ((a : α) → (l : List α) → motive l → motive (cons a l)) →    -- cons case
    (l : List α) → motive l

If `motive` lands in `Type`, you get *recursion*: define functions like
`length`, `append`, `map`. If `motive` lands in `Prop`, you get
*induction*: prove `∀ l, P l` by handling the `nil` and `cons` cases.
This unification of recursion and induction is the Curry–Howard
correspondence: programs and proofs are the same machinery.
-/

-- Recursion (motive : List α → Type)
def myLength : List Nat → Nat
  | []      => 0
  | _ :: xs => myLength xs + 1

-- Induction (motive : List α → Prop)
theorem length_nonneg (l : List Nat) : 0 ≤ myLength l := by
  induction l with
  | nil         => exact Nat.le_refl 0
  | cons _ _ ih => exact Nat.le_succ_of_le ih

/-
Q4. What is the iota rule?

The iota rule (ι-rule) is the *computation rule* for inductive types:
when a recursor meets a constructor, it reduces.

For `List`, ι gives exactly two reductions:

  List.rec  hnil  hcons  nil          ↦  hnil
  List.rec  hnil  hcons  (cons a l)   ↦  hcons a l (List.rec hnil hcons l)

Read in English: applying the recursor to `nil` selects the nil-branch;
applying it to `cons a l` selects the cons-branch and recurses on `l`.

Why this matters: when you define a function by pattern matching, Lean
compiles it down to `List.rec`. The ι-rule is what makes the defining
equations true *by computation* — no proof step required. That is why
`rfl` can close goals about concrete inputs.
-/

example : myLength [10, 20, 30] = 3 := rfl  -- ι unfolds everything to `3`

/-
The full family of reduction rules used by Lean's kernel to decide
definitional equality:

   Rule       Triggers on                  Example
   ────────── ──────────────────────────── ─────────────────────────
   β beta     (fun x => e) a               function application
   δ delta    a defined name               unfolding a `def`
   ι iota     recursor on a constructor    pattern-match step
   ζ zeta     let x := v; e                let-binding
   η eta      fun x => f x  ≡  f           definitional extensionality

ι is the one bound specifically to inductive types. It is the reason
that `simp`, `decide`, and bare `rfl` can make progress on recursively
defined functions applied to concrete data: the kernel just *runs*
the function, one ι-step per constructor.
-/

-- A worked ι trace for `myLength [10, 20, 30]`:
--   myLength (10 :: 20 :: 30 :: [])
-- ↦ι myLength (20 :: 30 :: []) + 1
-- ↦ι (myLength (30 :: []) + 1) + 1
-- ↦ι ((myLength [] + 1) + 1) + 1
-- ↦ι ((0 + 1) + 1) + 1
-- ↦  3

/-
Q5. What is the recursor and how does it work?

Every `inductive T` auto-generates `T.rec` — the *only* primitive way to
consume a value of T in pure CIC. Its principle:

  To define or prove something for every value of T, it suffices to handle
  each constructor, with induction hypotheses supplied for recursive args.

Pattern matching, `match`, the `induction` tactic, and structural recursion
all elaborate down to applications of `T.rec`.

General shape, for an inductive T with constructors c₁, …, cₙ:

  T.rec :
    {motive : T → Sort u} →                -- what to produce for each T
    (method₁ : … → motive (c₁ args)) →    -- one method per constructor
    …
    (t : T) → motive t

Each method takes the constructor's arguments plus, for every recursive
argument `r : T`, an extra IH of type `motive r`. The kernel supplies
those IHs automatically — you never recurse "by hand".

Two faces (Curry–Howard at the inductive level):
  motive : T → Type  →  recursion (define a function on T)
  motive : T → Prop  →  induction (prove a ∀-statement over T)
-/

#check @Nat.rec
-- @Nat.rec : {motive : Nat → Sort u_1} →
--   motive Nat.zero →
--   ((n : Nat) → motive n → motive (Nat.succ n)) →
--   (t : Nat) → motive t

-- `double` defined with only Nat.rec — no pattern matching, no recursion sugar:
def double : Nat → Nat :=
  Nat.rec 0 (fun _ ih => ih + 2)

example : double 5 = 10 := rfl   -- ι unfolds the whole thing

/-
Pattern matching is just sugar; `length` desugars to:

  def length : List α → Nat :=
    List.rec 0 (fun _ _ ih => ih + 1)   -- ih = length xs, supplied by rec

Variants Lean generates alongside `T.rec`:
  T.recOn        same as rec, target as the first explicit arg (ergonomic)
  T.casesOn      rec without IHs — discriminate only, don't recurse
  T.brecOn       "below" recursion: full tree of sub-values, for non-
                 structural recursion (e.g. recursing on `n / 2`)
  T.noConfusion  "different constructors are distinct" — powers `injection`

Design note: the kernel knows one rule per inductive (its recursor) plus
ι-reduction. Everything else (`match`, `induction`, `cases`, structural
recursion) is the elaborator translating user syntax into recursor calls.
-/

/-
Q6. What *is* the elaborator?

The elaborator is the bridge between what you write and what the kernel
sees. Lean is deliberately built in two layers:

     your code  (surface syntax)
         │   rich, ergonomic: notation, _, implicits, [Inst], dot,
         │   do-notation, tactics, macros, ...
         ▼
     ┌──────────────┐
     │  ELABORATOR  │   walks your syntax, produces a fully-typed core term
     └──────────────┘
         │   every implicit filled, every overload resolved,
         │   every macro expanded
         ▼
     core term  (CIC: lambdas, Π-types, universes, applications, axioms)
         │
         ▼
     ┌──────────────┐
     │    KERNEL    │   tiny, trusted type-checker — verifies the core term
     └──────────────┘

What it does, concretely, in a single traversal of your syntax tree:

  - Sees `_` or an implicit slot       → invents a metavariable `?m.N`.
  - Sees `a + b`                       → looks up the `HAdd` instance and
                                         rewrites to `HAdd.hAdd a b`.
  - Sees `xs.length`                   → resolves to `List.length`/
                                         `String.length`/... based on `xs`.
  - Sees a numeric literal `2`         → wraps in `OfNat.ofNat` and
                                         resolves the instance.
  - Sees an ascription `(e : T)`       → adds `typeOf e ≡ T` to unification.
  - Sees a coercion site (e.g. ℕ → ℤ)  → inserts `Coe.coe`.
  - Sees a tactic block `by ...`       → runs the tactic, which itself
                                         produces a core term.
  - Continuously runs *unification* to solve metavariables against the
    accumulated constraints. Unsolved ones surface as `?m.N` in messages.

Why two layers? — the de Bruijn criterion: keep the *trusted* base small.
The elaborator is enormous and heuristic, but its output is re-checked by
the kernel. The kernel is a few thousand lines implementing a well-studied
calculus (CIC). All the ergonomic magic (typeclasses, `do`, notation,
tactics, `simp`, decision procedures) lives in the elaborator and need
*not* be trusted logically — the kernel catches anything malformed.

The Lean 4 twist: the elaborator is itself written in Lean and is
user-extensible. `notation`, `syntax`, `macro_rules`, `elab`, and tactics
all hook into it. That is why "the language" and "the metalanguage" are
the same language in Lean 4.

One-line summary:
   The elaborator takes your friendly, sugar-laden, ambiguous syntax and
   produces a single, fully-typed, kernel-checkable term — by inferring
   implicits, resolving overloads, running unification, and expanding
   macros and tactics along the way.
-/

-- A few quick observations of the elaborator at work:
#check (List.nil)              -- [] : List ?m.N        — implicit α stayed unresolved
#check (List.nil : List Nat)   -- [] : List Nat         — ascription pinned α
#check 1 + 2                   -- Nat                   — HAdd instance picked + literal defaulted
#check (1 + 2 : Int)           -- Int                   — ascription redirected both choices
