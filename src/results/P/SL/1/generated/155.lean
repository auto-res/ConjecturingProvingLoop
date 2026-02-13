

theorem Topology.interior_union_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hInt : interior A ⊆ interior (A ∪ B) := interior_mono hsubset
      exact hInt hA
  | inr hB =>
      have hsubset : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hInt : interior B ⊆ interior (A ∪ B) := interior_mono hsubset
      exact hInt hB