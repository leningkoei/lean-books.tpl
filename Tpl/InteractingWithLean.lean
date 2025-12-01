/-!
# Chapter6. Interacting with Lean
-/

/-!
## Section6.1. Messages
-/
section Messages

/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in -- Use `#guard_msgs` to avoid print error infomation, the doc
-- comment above it is necessary and must same with error imformation.
def x : Nat := "Not a number"

/--
error: aborting evaluation since the expression depends on the 'sorry' axiom,
which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval (sorry : Nat)

/--
error: aborting evaluation since the expression depends on the 'sorry' axiom,
which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs(error) in
/--
warning: declaration uses 'sorry'
-/
#guard_msgs(warning) in --← You can remove this pair of `#guard_msgs`, and
--↑ compiler will display warning message because of using `sorry`.
#eval (sorry : Nat)

end Messages

/-!
## Section6.2. Importing Files
-/
section ImportingFiles
end ImportingFiles

/-!
## Section6.3. More on Sections
-/
section MoreOnSections

section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by simp [double]

#check t1 y
#check t1 y x
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double]
  simp [Nat.add_mul]
end

end MoreOnSections

/-!
## Section6.4. More on namespaces
-/
section MoreOnNamespace

/-!
### `protected def`
-/
section

protected def Foo.bar : Nat := 1

/--
error: Unknown identifier `bar`
-/
#guard_msgs in
#check bar --← Because of `protected def`, you only can use `bar` though
--↑ `Foo.bar`.

/--
error: Invalid dotted identifier notation: The expected type of `.bar` could not
be determined
-/
#guard_msgs in
#check .bar --← Because of `protected def`, you only can use `bar` though
--↑ `Foo.bar`.

#check Foo.bar

end

/-!
### `open`
-/
section

section
open Nat (succ zero gcd)
#check zero
#eval gcd 15 6
end

section
open Nat hiding succ gcd
#check zero

/--
error: Unknown identifier `gcd`
-/
#guard_msgs in
#eval gcd 15 6

#eval Nat.gcd 15 6
end

section
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3

/--
error: Unknown identifier `add`
-/
#guard_msgs in
#eval add (mul 2 2) 3
end

namespace l1

  namespace l2

    namespace l3

      def foo := 1

    end l3
    
    #check l3.foo
    export l3 (foo) --← Export `l3.foo` to `l2.foo`, cannot access `foo` though
    --↑ `l3.foo` in `l1` or other namespace any more.
    #check l3.foo

  end l2

  /--
  error: Unknown identifier `foo`
  -/
  #guard_msgs in
  #check foo
  
  #check l2.foo
  
  /--
  error: Unknown identifier `l3.foo`
  -/
  #guard_msgs in
  #check l3.foo
  
end l1

end

end MoreOnNamespace

/-!
## Section6.5 Attributes
-/
section Attributes

def isPrefix {α : Type} (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t : List α, l₁ ++ t = l₂

#check List.append_nil
-- @[simp]
theorem List.isPrefix_self {α : Type} (as : List α) : isPrefix as as := by
  show ∃ t : List α, as ++ t = as
  apply Exists.intro []
  rw [List.append_nil]

section
attribute [local simp] List.isPrefix_self
example : isPrefix [1, 2, 3] [1, 2, 3] := by simp
end

/-- error: `simp` made no progress -/
#guard_msgs in
example : isPrefix [1, 2, 3] [1, 2, 3] := by simp

-- namespace test
-- instance : LE (List α) where --← Will effect all namespaces.
--   le := isPrefix
-- example (as : List α) : as ≤ as := as.isPrefix_self
-- end test
-- example (as : List α) : as ≤ as := as.isPrefix_self

def instLe : LE (List α) where
  le := isPrefix

section
attribute [local instance] instLe --← Just effect this section.
example (as : List α) : as ≤ as := as.isPrefix_self
end
/--
error: failed to synthesize
  LE (List α)

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command.
-/
#guard_msgs() in
example (as : List α) : as ≤ as := as.isPrefix_self

end Attributes

/-!
## Section6.6. More on Implicit Arguments
-/
section MoreOnImplicitArguments

namespace NoWeekImplicitArguments
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ a : α, r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
: symmetric r := by
  -- show ∀ {a b : α}, r a b → r b a
  intro ha hb
  intro h
  apply euclr h
  exact reflr ha

theorem th2 {α : Type u} {r : α → α → Prop}
  (symmr : symmetric r) (euclr : euclidean r)
: transitive r := by
  intro ha hb hc
  intro h₁ h₂
  apply symmr    -- ⊢ r hc ha
  apply euclr h₂ -- ⊢ r hb ha
  apply symmr    -- ⊢ r ha hb
  exact h₁

theorem th3 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
: transitive r := th2 (th1 reflr euclr) @euclr
--↑ symbol`@`: Disable Implicit Arguments
end NoWeekImplicitArguments
namespace WeekImplicitArguments
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ a : α, r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ ⦃a b : α⦄, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c : α⦄, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c : α⦄, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
: symmetric r := by
  -- show ∀ {a b : α}, r a b → r b a
  intro ha hb
  intro h
  apply euclr h
  exact reflr ha

theorem th2 {α : Type u} {r : α → α → Prop}
  (symmr : symmetric r) (euclr : euclidean r)
: transitive r := by
  intro ha hb hc
  intro h₁ h₂
  apply symmr    -- ⊢ r hc ha
  apply euclr h₂ -- ⊢ r hb ha
  apply symmr    -- ⊢ r ha hb
  exact h₁

theorem th3 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
: transitive r := th2 (th1 reflr euclr) euclr
end WeekImplicitArguments
namespace NoImplicitArguments
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ a : α, r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a b : α), r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a b c : α), r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a b c : α), r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
: symmetric r := by
  -- show ∀ (a b : α), r a b → r b a
  intro ha hb
  intro h
  apply euclr ha hb ha h
  apply reflr

theorem th2 {α : Type u} {r : α → α → Prop}
  (symmr : symmetric r) (euclr : euclidean r)
: transitive r := by
  intro ha hb hc
  intro h₁ h₂
  apply symmr hc ha       -- ⊢ r hc ha
  apply euclr hb hc ha h₂ -- ⊢ r hb ha
  apply symmr ha hb       -- ⊢ r ha hb
  exact h₁

theorem th3 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
: transitive r := th2 (th1 reflr euclr) euclr
end NoImplicitArguments

end MoreOnImplicitArguments

/-!
## Section6.7. Notation
-/
section Notation
-- Too complex... I will come back here when I have problem with "Notation"
-- every time.
end Notation

/-!
## Section6.8. Coercions
-/
section Coercions

variable (m n : Nat)
variable (i j : Int)

#check i + ↑m -- Notation `↑`.
#check i + Int.ofNat m + j -- Method `Int.ofNat`.
#check i + m + n -- Lean's automatic coercions.

end Coercions

/-!
## Section6.9. Displaying Infomation
-/
section DisplayingInfomation
end DisplayingInfomation

/-!
## Section6.10. Setting Options
-/
section SettingOptions
end SettingOptions

/-!
## Section6.11. Using the Library
-/
section UsingTheLibrary
end UsingTheLibrary

/-!
## Section6.12. Auto Bound Implicit Arguments
-/
section AutoBoundImplicitArguments
end AutoBoundImplicitArguments

/-!
## Section6.13. Implicit Lambdas
-/
section ImplicitLambdas
end ImplicitLambdas

/-!
## Section6.14. Sugar for Simple Functions
-/
section SugarForSimpleFunctions
end SugarForSimpleFunctions

/-!
## Section6.15. Named Arguments
-/
section NamedArgument
end NamedArgument

