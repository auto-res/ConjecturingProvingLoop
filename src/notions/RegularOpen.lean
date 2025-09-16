import Mathlib

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- A set `s` is called **regular open** if it is equal to the interior of its closure. -/
def IsRegularOpen (s : Set X) : Prop :=
  interior (closure s) = s

/-- A set `s` is called **regular closed** if it is equal to the closure of its interior. -/
def IsRegularClosed (s : Set X) : Prop :=
  closure (interior s) = s

theorem regular_open_interior_of_regular_open_ai (s : Set X) (hs : IsRegularOpen s) : interior s = s := by
  /-
  We need to show that for a set \( s \) in a topological space \( X \), if \( s \) is regular open, then the interior of \( s \) is equal to \( s \). Given that \( s \) is regular open, by definition, \( \text{interior}(\text{closure}(s)) = s \). We will use this property to derive that \( \text{interior}(s) = s \).
  1. Start with the given property \( \text{interior}(\text{closure}(s)) = s \).
  2. Since \( s \) is regular open, we know that \( \text{closure}(s) \) is closed.
  3. The interior of a closed set is open and equals the set itself if the set is also regular open.
  4. Therefore, \( \text{interior}(s) = s \).
  -/
  -- We need to show that the interior of `s` is equal to `s`.
  have h : interior (closure s) = s := hs
  -- Since `s` is regular open, we know that the closure of `s` is closed.
  -- The interior of a closed set is open and equals the set itself if the set is also regular open.
  -- Therefore, we can directly use the given property `h` to conclude that `interior s = s`.
  rw [← h]
  -- Simplify the expression to show that `interior s = s`.
  simp


theorem regular_closed_complement_ai (s : Set X) : IsRegularOpen (sᶜ) → IsRegularClosed s := by
  /-
  We aim to show that if a set \( s \) is regular open, then its complement \( s^c \) is regular closed. Conversely, if a set \( s \) is regular closed, then its complement \( s^c \) is regular open. This is a consequence of the duality between open and closed sets in a topological space.
  1. **Regular Open implies Regular Closed**:
     - Given \( s \) is regular open, we have \( \text{interior}(\text{closure}(s)) = s \).
     - Consider the complement \( s^c \). We need to show that \( s \) is regular closed, i.e., \( \text{closure}(\text{interior}(s)) = s \).
     - Since \( s \) is regular open, \( s = \text{interior}(\text{closure}(s)) \).
     - Taking the complement, \( s^c = (\text{interior}(\text{closure}(s)))^c \).
     - By the properties of complements, \( (\text{interior}(\text{closure}(s)))^c = \text{closure}(s^c) \).
     - Therefore, \( s^c = \text{closure}(s^c) \), which means \( s \) is regular closed.
  2. **Regular Closed implies Regular Open**:
     - Given \( s \) is regular closed, we have \( \text{closure}(\text{interior}(s)) = s \).
     - Consider the complement \( s^c \). We need to show that \( s^c \) is regular open, i.e., \( \text{interior}(\text{closure}(s^c)) = s^c \).
     - Since \( s \) is regular closed, \( s = \text{closure}(\text{interior}(s)) \).
     - Taking the complement, \( s^c = (\text{closure}(\text{interior}(s)))^c \).
     - By the properties of complements, \( (\text{closure}(\text{interior}(s)))^c = \text{interior}(s^c) \).
     - Therefore, \( s^c = \text{interior}(s^c) \), which means \( s^c \) is regular open.
  -/
  intro h
  rw [IsRegularClosed] -- Rewrite the definition of regular closed set
  rw [IsRegularOpen] at h -- Rewrite the definition of regular open set for the complement
  simp_all -- Simplify the expressions using the properties of complements and set operations
  <;> aesop -- Use the Aesop tactic to handle the logical implications and equivalences


theorem regular_closed_closure_of_regular_closed_ai (s : Set X) (hs : IsRegularClosed s) : closure s = s := by
  /-
  We need to show that for a set \( s \) in a topological space \( X \), if \( s \) is regular closed, then its closure is equal to \( s \). By definition, a set \( s \) is regular closed if the closure of its interior is equal to \( s \). Given that \( s \) is regular closed, we can directly use this definition to conclude that the closure of \( s \) is \( s \).
  -/
  -- Since `s` is regular closed, by definition, the closure of its interior is equal to `s`.
  have h : closure (interior s) = s := hs
  -- We need to show that the closure of `s` is equal to `s`.
  apply Eq.symm
  -- Using the fact that the closure of the interior of `s` is `s`, we can conclude that the closure of `s` is `s`.
  rw [← h, closure_closure]
