

theorem Topology.interiorClosure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : closure A ⊆ closure (A ∪ B) := by
        have hA_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono hA_subset
      exact (interior_mono h_subset) hxA
  | inr hxB =>
      have h_subset : closure B ⊆ closure (A ∪ B) := by
        have hB_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono hB_subset
      exact (interior_mono h_subset) hxB