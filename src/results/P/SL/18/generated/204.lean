

theorem dense_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → Dense (B : Set X) → Dense (A ∪ B : Set X) := by
  intro hDenseA hDenseB
  -- Density of `A` already suffices to make the union dense.
  have h₁ : Dense (A ∪ B : Set X) :=
    Topology.dense_union_left (A := A) (B := B) hDenseA
  -- Using the density of `B` provides the same conclusion, ensuring both
  -- hypotheses are acknowledged.
  have _h₂ : Dense (A ∪ B : Set X) :=
    Topology.dense_union_right (A := A) (B := B) hDenseB
  exact h₁