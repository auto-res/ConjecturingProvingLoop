

theorem interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B) := by
  intro x hxB
  -- `interior` is monotone with respect to set inclusion.
  have h_subset : (B : Set X) ⊆ (A ∪ B : Set X) := by
    intro y hy
    exact Or.inr hy
  exact (interior_mono h_subset) hxB