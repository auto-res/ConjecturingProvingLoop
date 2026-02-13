

theorem interior_inter_interior_subset_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hA, hB⟩
  -- The set `U = interior A ∩ interior B` is an open neighbourhood of `x`
  -- contained in `A ∩ B`.
  have hU_open : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  have hU_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro y hy
    exact ⟨interior_subset hy.1, interior_subset hy.2⟩
  -- Hence `x` belongs to the interior of `A ∩ B`.
  exact
    (Set.mem_interior).2 ⟨interior A ∩ interior B, hU_open, hU_subset, ⟨hA, hB⟩⟩