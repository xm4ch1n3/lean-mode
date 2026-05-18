/-
 ____      ___
|___ \    ( _ )
  __) |   / _ \
 / __/  _| (_) |
|_____|(_)\___/
-/
/-
1. What makes dependent type theory dependent? (really good question)
Let's unpack this.

Parameters come in a few flavors:

Syntax   Kind      Behavior
(x : T)  explicit  you pass it                      (a)
{x : T}  implicit  Lean infers it                   (b)
[x : T]  instance  typeclass resolution fills it    (c) -- see below EXAMPLE_(c)

They said that "types can depend on parameters." What does that mean?  A few escalating examples:

(i) Ordinary (non-dependent): types don't depend on values
def add (x : Nat) (y : Nat) : Nat := x + y
-- y's type (Nat) doesn't depend on x

(ii) Type depending on a TYPE parameter (polymorphism, mild dependence)
def id (α : Type) (x : α) : α := x
-- x's type is α, which is the *value* of the previous parameter

(iii) Type depending on a VALUE parameter (full dependent types)
def replicate (n : Nat) (x : String) : Vector String n := ...

-- the return type mentions n; different n gives a different type, so:
  Vector String 0  : Type   -- the type of "string vectors of length 0"
  Vector String 3  : Type   -- the type of "string vectors of length 3"
  Vector String 5  : Type   -- the type of "string vectors of length 5"
-/
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as -- Note that this is precisely (ii)) -- the type of cons is polymorphic in α, but it doesn't depend on `a` or `as` as it would in (iii)

#check cons Nat
#check cons Bool
#check cons

--- EXAMPLE_(c)
def showIt {α : Type} [ToString α] (x : α) : String := toString x  -- Looks like a cast, but it's not; it's Rust's `trait bound` equivalent.
                                                                   -- It says: "require that the type α has an instance of the typeclass `ToString`
                                                                   -- (i.e., a known way to produce a String from α). Lean will find and pass that
                                                                   -- instance silently, which makes the method `toString : α → String` available
                                                                   -- in the body."

#eval showIt 42        -- "42"
#eval showIt true      -- "true"
#eval showIt "hi"      -- "hi"
#eval showIt [1, 2, 3] -- "[1, 2, 3]"

-- 2. What is a typeclass?
--    => A named interface (a set of operations) that a type can later be declared to satisfy.
---------------

example : ((a : α) → β) = (α → β) := rfl -- "When β doesn't depend on a, (a : α) → β is no different from the type α → β"

#check @List.cons   -- @List.cons : {α : Type u_1} → α → List α → List α
#check @List.nil    -- @List.nil : {α : Type u_1} → List α
#check @List.length -- @List.length : {α : Type u_1} → List α → Nat
#check @List.append -- @List.append : {α : Type u_1} → List α → List α → List α

def xs := [1, 2, 3]
#eval List.length xs         -- 3
#eval xs.length              -- 3
#eval List.cons 0 xs         -- [0, 1, 2, 3]
#eval xs.cons 0              -- [0, 1, 2, 3]
#eval List.append xs [4, 5]  -- [1, 2, 3, 4, 5]
#eval xs.append [4, 5]       -- [1, 2, 3, 4, 5]
#eval xs ++ [4, 5]           -- [1, 2, 3, 4, 5]

-- 3. What is a dependent function type?
-- => "dependent function types (a : α) → β a generalize the notion of a function type α → β by allowing β to depend on a"

universe u v -- SHIFT + K + K on `universe` to see the docs

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a := ⟨a, b⟩
def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a := Sigma.mk a b

def h1 (x : Nat) : Nat := (f Type (fun α => α) Nat x).2
def h2 (x : Nat) : Nat := (g Type (fun α => α) Nat x).2

#eval h1 5
#eval h2 5
example : h1 = h2 := rfl
-- 4. Why is the result "5"?
/-
Step-by-step for `#eval h1 5`:

h1 5 = (f Type (fun α => α) Nat 5).2

Match f's parameters:
----------------------------------------------------------------------
f's param       type                    got
----------------------------------------------------------------------
α : Type u      a type                  Type
β : α → Type v  a function Type → Type  fun α => α (identity on types)
a : α           a Type                  Nat
b : β a         (fun α => α) Nat = Nat  5
----------------------------------------------------------------------

Body: ⟨a, b⟩ = ⟨Nat, 5⟩ -- a dependent pair where:
- 1st component (.1) is the type Nat
- 2nd component (.2) is the value 5 : Nat
Result type: (a : Type) × (fun α => α) a -- the first component is a type, and the second is a value of that type.
Then .2 projects → 5.
-/

/-
 ____     ___
|___ \   / _ \
  __) | | (_) |
 / __/  _\__, |
|_____|(_) /_/
-/

/-
Glossary (terms used throughout this section):

  elaborator    The Lean pass that turns surface syntax into fully typed core terms:
                inserts implicit arguments, resolves overloads, runs unification.
  bare X        The identifier X written alone — no parens, no @, no ascription, no
                application. `List.nil` is bare; `(List.nil)`, `@List.nil`, `List.nil 0`
                are not. `#check` treats bare identifiers specially (prints signature).
  signature     The declared type of a definition, with its original binders visible
                (including implicit `{α}` slots). Bare `#check name` shows this.
  metavariable  A placeholder `?m.N` the elaborator creates for an unknown implicit.
                Resolved by unification; if nothing constrains it, it stays unresolved
                (you'll see it in the output as `?m.1`, etc.).
  ascription    The syntax `(e : T)` — tells the elaborator "treat e as having type T".
                Used to disambiguate or to *pin* implicits.
  overload      One name with multiple definitions; the elaborator picks which one
                based on context. Examples: `+` works for Nat/Int/Float/String via the
                `HAdd` typeclass; the literal `2` can be Nat/Int/Float; dot notation
                `xs.length` picks `List.length` or `String.length` based on `xs`'s type.
  pinning       Giving the elaborator a constraint that forces a metavariable to a
                specific value. Most commonly done via ascription: `(List.nil : List Nat)`
                pins α to Nat.
  implicit arg  An argument declared with `{α : T}` (or `[α : T]` for instances) —
                supplied by the elaborator instead of the caller.
  unification   The elaborator's algorithm for solving equations between types (and
                terms) — e.g. matching `List ?m.1` against `List Nat` solves `?m.1 := Nat`.
-/

/-
1. What is section 2.9 really about?

Implicit arguments. The whole section reduces to one idea: "type arguments
are usually redundant; here are four knobs for who supplies them."

  Knob          Who supplies α                       Declaration                  Call site
  ------------- ------------------------------------ ---------------------------- --------------
  (α : Type)    the caller, always                   def f (α : Type) (x : α)     f Nat 0
  _             the elaborator, on demand            (unchanged)                  f _ 0
  {α : Type}    the elaborator, by default           def f {α : Type} (x : α)     f 0
  @f            escape hatch: all implicits explicit (unchanged)                  @f Nat 0

Everything else in the section (variable {α}, type ascription (e : T),
numeral defaulting to Nat) is ergonomic glue around these four knobs.
-/

-- All four knobs on the same toy function:
def myId1 (α : Type) (x : α) : α := x       -- explicit α
def myId2 {α : Type} (x : α) : α := x       -- implicit α

#check myId1 Nat 0          -- caller passes Nat explicitly
#check myId1 _ 0            -- caller defers to elaborator with _
#check myId2 0              -- elaborator infers Nat silently from 0 : Nat
#check @myId2 Nat 0         -- @ flips implicits back to explicit
#check @myId2               -- @myId2 : {α : Type} → α → α (shows hidden args)

-- Ergonomic glue: ascription pins the type when context is too thin.
#check (List.nil : List Nat)   -- [] : List Nat   (otherwise α is unknown)
#check (2 : Int)               -- 2 : Int         (otherwise numerals default to Nat)

-- `variable {α}` lets a whole section share an implicit without repeating it.
section
  variable {α : Type}
  variable (x : α)
  def myId3 := x   -- elaborated as: def myId3 {α : Type} (x : α) : α := x
end

#check @myId3       -- @myId3 : {α : Type} → α → α
