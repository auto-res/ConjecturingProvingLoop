

theorem Topology.union_interior_subset_interior_union'
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A` is contained in `interior (A ∪ B)` by monotonicity.
      have h_mono : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have h_int_mono : interior A ⊆ interior (A ∪ B) := interior_mono h_mono
      exact h_int_mono hA
  | inr hB =>
      -- `interior B` is contained in `interior (A ∪ B)` by monotonicity.
      have h_mono : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have h_int_mono : interior B ⊆ interior (A ∪ B) := interior_mono h_mono
      exact h_int_mono hB