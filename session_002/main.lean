/-
 ____      _
|___ \    / |
  __) |   | |
 / __/  _ | |
|_____|(_)|_|
-/
def m : Nat  := 0
def n : Nat  := 1
def t : Bool := true
def f : Bool := false
/-
(*) 1. Why does replacing Bool with Prop still hold?
(*) 2. What if you instead write:
  def t: Prop := True <-- What does this mean?
-/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check t
#check t && f -- "&&" is the Boolean and
#check t ∧ f
#check t || f
#check t ∨ f
/-
(*) 3. Why ∧/∨ turns the information into a Prop? Why is f = true?
-/
#check true -- Boolean "true"
#check True

-- #eval is straightforward

/-
"What makes simple type theory powerful is that you can build new types out of others."

Ok, so the compiler is messy. If there's nothing but comments following a type of × or →, I get no error, but adding a new line with anything
makes the error visible; it asks me to provide an expected ':=', 'where' or '|'.
So:
4. How do you := default values? and
5. What exactly are 'where' or '|' besides ':='?
-/

-- A] Look at →
-- a) Use 'default' (canonical); this ignores its input (domain) and only works when its output (codomain) has a default instance
def p1 : Nat → Int := default -- = 0
-- b) Or anonymous (i.e. lambda) functions
def p2: Nat → Int := fun n => Int.ofNat n
def p3: (p : Nat) → Int := fun _ => Int.ofNat n -- syntactic sugar for lambdas
-- c) Or constant functions
def p4: Nat → Int := fun _ => -1
-- d) Or eta-reduced (i.e. the 'n' doesn't appear anywhere; p2 is eta-expanded in this view, but p3 is not because it discards with '_' its input,
--    when in fact it should forward it: 'fun _' to 'fun n'
def p5: Nat → Int := Int.ofNat
-- e) Or keep the scope openended with 'sorry' (i.e. I want a placeholder here while I keep developing; lets me continue type checking, but panics at runtime)
def p6: Nat → Int := sorry

-- B] Look at ×
-- a) 'default' works here too
def q1 : Nat × Int := default -- = (0, 0)
-- b) Or anonymous (tuple syntax)
def q2 : Nat × Int := (3, -7)
-- c) Or explicit constructor
def q3 : Nat × Int := Prod.mk 3 (-7)
-- 3. Or anonymous constructor brackets (type ⟨ with \< and ⟩ with \>)
def q4 : Nat × Int := ⟨3, -7⟩ -- in this case it's the same as q2, but normally it would be used like this:
/-
structure Person where name : String; age : Nat
Person.mk          -- 'mk' is convention, as far as I understand
Person.mk "Ada" 36 -- explicit call
⟨"Ada", 36⟩        -- shorthand, same as above
-/

/-
On 5.
':=', '|' and 'where' are 3 different ways of creating a body. Briefly:
--1] ':=' - the body is one expression (all the examples above, essentially)

--2] '|'  - pattern matching clauses
def length : List α → Nat
  | []      => 0             (1)
  | _ :: xs => 1 + length xs (2)

'::' stands for 'head :: tail', so in this case we discard the head, keep the rest
'::' is right-associative, so 1 :: 2 :: 3 :: [] => 1 :: (2 :: (3 :: []))

* input: []                     =>  match (1)              => returns 0
* input: [1, 2, 3] = 1 :: [2,3] =>  match (2); xs = [2, 3] => returns 1 + 2

The above is shorthand for:

def length (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: xs => 1 + length xs

--3] 'where' - attach local helpers, in scope of the body
def sumTo (n : Nat) : Nat := go n 0
where
  go : Nat → Nat → Nat                -- note that we match against 2 inputs, but in this case only the first does real work:
    | 0,   acc => acc                 -- clause 1: 0;   clause 2: k+1 => case split
    | k+1, acc => go k (acc + (k+1))  -- clause 1: acc; clause 2: acc => same in both, only binds acc in both cases

(*) Is this closure?
* 'go' helper is private to 'sumTo';
* 'where' always follows a body (a := body or a |‑clause body);
* 'where' does not replace the body, it augments it;
-/

/-
6. What exactly does it mean "to range over types"?
E.g. 'n' in 'n + 1' ranges over numbers, and 'α' in 'List α' ranges over types (it can be Nat, Bool, etc.)
Convention:
-- lowercase Greek: type variables
-- lowercase Latin: value variables
-- uppercase Latin: type names / propositions
-/

#check Nat → Nat → Nat
#check Nat → (Nat → Nat) -- this enables currying (ie. partial func application)
#check (Nat → Nat) → Nat -- the 2 above are identical, this one is not because → is right-associative (same as ::)

#check Nat.add
#check Nat.add 3     -- note the Nat → Nat
#eval Nat.add 3 5    -- 8 : add(3)(5) <----------------------
#eval Nat.add 3 n    -- generalized                          \
def addPair : Nat × Nat → Nat := fun (a, b) => a + b  --     |
#eval addPair (3, 5) -- 8 : add(3, 5) <----------------------

#check (m, n)
#check (m, n).1
#check (m, n).2
def a2 : Nat := 2
def a3 : Nat := 3
#eval (m, n, a2, a3).2.2.2 -- to get a3 (disgusting! use 'structure')

 /-
 ____      ____
|___ \    |___ \
  __) |     __) |
 / __/  _  / __/
|_____|(_)|_____|
-/

/-
One way in which Lean's dependent type theory extends simple type theory is that types themselves—entities like Nat and Bool—are first-class citizens,
which is to say that they themselves are objects. For that to be the case, each of them also has to have a type.
-/
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod -- again, why is Prod who takes pairs 3 types?
--     |---------|   |---|
--        input     output
#check G α β -- I expect Nat × Bool
example : G α β = (Nat × Bool) := rfl -- by reflexivity
/-
Here's a detour regarding constructors. Let's look at Bool, which Lean defines like:

inductive Bool : Type where
  | false : Bool
  | true : Bool

7. Does this subtly point to set theory, as in if Bool is false/true, then you getting a type Bool can only materialize into an op of the same set?
Well, apparently this question points to the difference between *set theory* and *type theory*!
The difference lies in where do the elements come from?
- Set theory:  The Universe already exists, full of stuff and Bool = {0, 1} just picks two pre-existing objects and puts a label on a box, but
               the number 0 doesn't care that it's a Bool.
               => selection from pre-existing universe
- Type theory: There is no universal soup of values, and Bool creates its inhabitants via the constructors false and true. These don't exist
               before Bool is defined, and they cannot inhabit any other type unless you explicitly define a coercion.
               => generation from rules

For Bool the distinction feels trivial because both have exactly two elements. But for Nat it matters: in set theory Nat is "some infinite subset of the universe"; in type theory Nat is exactly the terms you can build with 'zero' and 'succ'.

8. So the proof by induction works because the type *is* the inductive construction?
Yes!

More detours, to cover:

9. When we say every Nat is literally a finite tree (or a finite tower of consecutive 'succ'), does that mean it's stored that way?
   What about huge numbers like 2^512?
   How does Lean know the chain length of succ for a Nat?
Part of the answer: think in terms of what happens at
- runtime?
  -- 2^512 is a GMP integer (https://gmplib.org/)
- logical level?
  -- 2^512 is a huge tower of succ
- proof level?
  -- 2^512 is handled by that recursor, in this case Nat.rec (10.2)

10. How does induction work without asserting it as an axiom (how exactly is it constructive)?
I think it comes down to understanding these 2 things:
10.1 What is a recursor? E.g.: https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=peano-axioms
10.2 How does induction fall from the recursor as a finite theorem?
-/
#check 2^512
#eval  2^512

/-
#check SomeType : Type

What is Type?
-/
#check Type 0
#check Type 1
#check Type 2
-- ...
/-
11. What does it mean that Lean's underlying foundation has an infinite hierarchy of types?
If the type of Type would have been Type, you run into the Russell's paradox for types, i.e. Girard's paradox:
https://en.wikipedia.org/wiki/System_U#Inconsistency_and_Girard's_paradox
So, creating this tower of types prevents self-referential type membership loops, so no universe contains itself.

12. Ok, but what is the relationship between Sort and Type?

Sort 0  --  Prop   : the universe of propositions
Sort 1  --  Type   : the universe of small data types
Sort 2  --  Type 2 : bigger types
Sort u  --  Type u : level u

13. Why Sort?
Very confusing name. It comes from "many-sorted logic", and "sorts" is similar to "kinds" or "categories". I think about it like this:
A variable of type Bool can't be confused with one of type Nat, even though both Nat and Bool live in the same Sort (Sort 1).
Each variable has a type, and each type has a sort.
Thus, a Sort n is a universe of types and Sort is an infinite family of universes.

Reading DOWN a column: a sort (universe) contains a type, which contains a term.
Reading ACROSS: bigger universes hold bigger types.

sort  Prop (Sort 0)   Type (Sort 1)   Type 1 (Sort 2)      Type 2 (Sort 3)        ...
-------------------------------------------------------------------------------------
type  True            Bool            Nat → Type           Type → Type 1          ...
term  True.intro      true            fun n => Fin n       fun (_ : Type) => Type ...
-/
#check Sort 0
/-
14. Wait, what? I don't have a mental model for this. Each sort has a ...type?
The type of 'Prop' is 'Type' and the type of 'Sort 0' is also 'Type', so they both have the same type, but 'Sort 0' is a universe of all 'Prop', so are we saying that
the universe's type is the type of one of its elements...?
This confusion can only be resolved if Sort 0 = Prop, so Prop is the universe itself.
-/
example : Sort 0 = Prop := rfl -- and indeed is right
example : Sort 1 = Type := rfl
#check Nat → Prop -- since we're here... quick check: why is this of type 'Type'?
                  -- because the function type must be at least as big as its biggest piece.

-- Polymorphism
#check List
universe u
def Q (α : Type u) : Type u := Prod α α
def Q'.{v} (α : Type v) : Type v := Prod α α
example : Q = Q' := rfl

