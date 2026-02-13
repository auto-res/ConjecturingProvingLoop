

theorem Topology.closure_union_subset
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_mono : closure A ⊆ closure (A ∪ B) := by
        have h_sub : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono h_sub
      exact h_mono hA
  | inr hB =>
      have h_mono : closure B ⊆ closure (A ∪ B) := by
        have h_sub : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono h_sub
      exact h_mono hB