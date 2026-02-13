

theorem interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior A ⊆ interior (closure B) := by
  -- First, upgrade the inclusion `A ⊆ B` to `A ⊆ closure B`.
  have h₁ : (A : Set X) ⊆ closure B := by
    intro x hx
    have : x ∈ B := hAB hx
    exact subset_closure this
  -- Monotonicity of `interior` yields the desired result.
  exact interior_mono h₁