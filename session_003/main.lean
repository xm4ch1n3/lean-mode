-- Small recap
def add_v1 (a: Nat) (b: Nat) : Nat := a + b               -- Named params version
def add (a: Nat) (b: Nat) := a + b                        -- Named params version, output Nat is inferred
def add_v2 : Nat → Nat → Nat := fun a b => a + b          -- Unnamed params version
-- lean is right associative so Nat → Nat → Nat is actually  Nat →  (Nat → Nat)
-- fun a b => a + b is syntactic sugar for
-- fun a => (fun b => a + b) 
-- so add_v2 3 is (fun a => (fun b => a + b)) 3 == fun b => 3 + b

def add3: Nat -> Nat := add_v2 3
#eval add3 5

/-
 ____      _____
|___ \    |___ /
  __) |     |_ \
 / __/  _  ___) |
|_____|(_)|____/
-/

def add5: Nat -> Nat := fun (x: Nat) => x + 5
#check add5
#check fun (x: Nat) => x + 5
#check λ (x: Nat) => x + 5 -- lambda typed \ lambda or \ fun  -> this convention is baked into the typing
#check λ x => x + 5 -- Nat is inferred, we can add only same types, no silet conversion
#check fun x => x + 5 -- fun instead of λ  

-- More func shaneanigans 
#eval (λ x : Nat => x + 3) 5 -- equivalent to add3 5  
-- Lambda functions are just like any other programming languages lambda functions: anonymous inline functions without names
-- in this case it is a value that sits in the Nat -> Nat type

def some_func_v1 (x: Nat)(y: Bool): Nat := if not y then x + 1 else x + 2 -- same as add_v1
def some_func_ (x: Nat)(y: Bool) := if not y then x + 1 else x + 2 -- Nat is inferred
#check some_func_v1 3 false
#eval some_func_v1 3 false
#eval some_func_v1 3 true
#check fun (x: Nat)(y: Bool) => if not y then x + 1 else x + 2 -- same function, only anonimous


def some_func_v2:  Nat → Bool → Nat := fun x y => if not y then x + 1 else x + 2 -- same as add_v2
#check some_func_v2 3 false
#eval some_func_v2 3 false
#eval some_func_v2 3 true
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2

-- Other examples I guess, same as line 22 - 26 examples
#check fun x : Nat => x
#check λ x : Nat => x
#check λ x => x

#check λ x : Nat => true
#check λ _ : Nat => true
#check λ _  => true

-- Function composition
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 3

def g_comp_f: Nat -> Bool := fun n => g (f (n))
#eval g_comp_f 123456
#eval g_comp_f 12
#check fun n : Nat => g (f n)
#check fun n => g (f n) -- again, Nat omitted and inferred
#eval (fun n : Nat => g (f n)) 123456
#eval (λ n : Nat => g (f n)) 12

--  Passing functions as parameters
def g_comp_f_v2 (g_func : String → Bool) (f_func : Nat → String) (x : Nat) :Bool := g_func (f_func x) 
--   def add_v1 (a:            Nat     ) (b:          Nat      )           :Nat  :=          a + b
--                           ^^^^ same as add_v1 but everything gets promoted to higher lever abstraction
--               g_func and a are values
--               String -> Bool and Nat are types
--               a      lives in (is a member of) Nat
--               g_func lives in (is a mmber of)  String → Bool
#eval g_comp_f_v2 g f 123456
#eval g_comp_f_v2 g f 12

def g_comp_f_v3 : (String → Bool) → (Nat → String) → Nat → Bool := fun g_func f_func x => g_func (f_func x) 
#eval g_comp_f_v3 g f 123456
#eval g_comp_f_v3 g f 12

-- Passing types as parameters
def g_comp_f_v4        (α : Type) (β : Type) (γ: Type) (g_func :      β → γ)    (f_func:    α → β)      (x: α)    :γ    := g_func (f_func x)
--  def g_comp_f_v2                                    (g_func : String → Bool) (f_func : Nat → String) (x : Nat) :Bool := g_func (f_func x)
--   !!! same higher level abstraction promotion
--    α , β, γ are types that live in Type1 but are also values !!!
--    g_func is a value that lives in β → γ
--    x is a value that lives in α 
#eval g_comp_f_v4 Nat String Bool g f 123456
#eval g_comp_f_v4 Nat String Bool g f 12

def g_comp_f_v5 (α β γ: Type) (g_func : β → γ) (f_func: α → β) (x: α) :γ := g_func (f_func x) -- simpler form
#eval g_comp_f_v5 Nat String Bool g f 123456
#eval g_comp_f_v5 Nat String Bool g f 12
/-
 ____      _  _
|___ \    | || |
  __) |   | || |
 / __/  _ |__  |
|_____|(_)   |_|
-/
-- We've already seen this:
def double (x : Nat) : Nat := x + x -- same as add_v1
#eval double 3
def double_v2 : Nat → Nat := fun x => x + x -- same as add_v2, output type inferred
#eval double_v2 3
def double_v3 : Nat → Nat := fun (x: Nat) => x + x -- same as add_v5
#eval double_v3 3

def pi := 3.141592654
-- def add (a: Nat) (b: Nat) := a + b -- we already have add defined on line 3
#eval add (double 3) (4 + 3)

def double_float (x: Float) : Float := 2 * x 
#eval double_float pi

def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval doTwice double 3

/-
 ____      ____
|___ \    | ___|
  __) |   |___ \
 / __/  _  ___) |
|_____|(_)|____/
-/
-- let is just a way to name an intermediate value so you don't repeat yourself
def twice_double (x : Nat) : Nat := let y := x + x; y * y -- y is scoped inside the function
#eval twice_double 3

def thrice_double (x : Nat) : Nat :=     --  ; ommited on line break
  let y := x + x
  y * y
#eval thrice_double 3

def foo := let a := Nat; fun x : a => x + 2 -- fine, lean replaces a with Nat
#eval foo 4

-- def bar := (let a:= Nat; fun a => fun x: a => x + 2) Nat -- failed to synthesize instance of type class
--  the 'fun a => ' shadows 'let a:= Nat'

/-
 ____      __
|___ \    / /_
  __) |  | '_ \
 / __/  _| (_) |
|_____|(_)\___/
-/
-- Main takeaway: variable defines any type throughout the whole file:
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def compose_full (α β γ: Type) (g :β → γ) (f: α → β) (x: α) :γ := g (f x) 
#eval compose Nat String Bool g f 123456
#eval compose Nat String Bool g f 12
#eval compose_full Nat String Bool g f 123456
#eval compose_full Nat String Bool g f 12

def executeTwice := h (h x)    
def executeTwice_full (α: Type) (h: α → α) (x: α) :α := h (h x) 
#eval executeTwice Nat twice_double 2 
#eval executeTwice_full Nat twice_double 2 

def executeThrice := h (h (h x))
def executeThrice_full (α: Type) (h: α → α) (x: α) :α := h ( h (h x)) 
#eval executeThrice Nat twice_double 2
#eval (1024 + 1024)^2

-- Section
section useful 
  variable (θ: Type) -- not available outside section scope
  def demo (x: θ) : θ := x
  #eval demo Nat 4
end useful

#eval demo Nat 4 -- demo still exists globally (no prefix) with θ baked in as an implicit argument
-- #eval θ -- Unknown identifier 'θ'
--
/-
 ____      _____
|___ \    |___  |
  __) |      / /
 / __/  _   / /
|_____|(_) /_/
-/
-- Lean provides you with the ability to group definitions into nested, hierarchical namespaces

-- Namespace
namespace Foo
  def a : Nat := 5
  def fnc (x : Nat) : Nat := x + 7
  #check a
  #eval fnc a

  def fa := fnc a
  def ffa := fnc (fnc a)

end Foo

-- #check a -- Unknown identifier 'a'
-- These need to use the namespace prefix
#check Foo.a
#check Foo.fa
#check Foo.ffa
#eval Foo.a
#eval Foo.fa
#eval Foo.ffa

open Foo  -- After this namespace prefix can be dropped
#check a
#check fa
#check ffa
#eval a
#eval fa
#eval ffa

-- Namespaces can be reopened
namespace Temp
  def temp_a := fun x => x + 1
end Temp
namespace Temp
  def temp_b := fun x => x + 2
end Temp

open Temp
#eval temp_a 1
#eval temp_b 1

