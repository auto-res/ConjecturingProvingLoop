

theorem Topology.P2_union_left_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- First, show that `interior (A ∪ B)` is dense in `X`.
  have h_dense_union : closure (interior (A ∪ B)) = (Set.univ : Set X) := by
    -- `closure (interior (A ∪ B)) ⊆ univ` is immediate.
    have h₁ : closure (interior (A ∪ B)) ⊆ (Set.univ : Set X) := by
      intro x _
      simp
    -- For the reverse inclusion, use the density of `interior A`.
    have h₂ : (Set.univ : Set X) ⊆ closure (interior (A ∪ B)) := by
      have h_cl_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have hA_subset : A ⊆ A ∪ B := by
            intro x hx
            exact Or.inl hx
          exact interior_mono hA_subset
        exact h_int_subset
      simpa [h_dense] using h_cl_subset
    exact subset_antisymm h₁ h₂
  -- Apply the lemma that `P2` holds for sets with dense interior.
  exact Topology.P2_of_dense_interior (X := X) (A := A ∪ B) h_dense_union