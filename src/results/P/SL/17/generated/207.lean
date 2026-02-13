

theorem Topology.interior_inter_isOpen_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    interior (A ∩ U) = interior A ∩ U := by
  -- First inclusion: `⊆`
  apply Set.Subset.antisymm
  · intro x hx
    have hA : x ∈ interior A := by
      have h_subset : (A ∩ U) ⊆ A := Set.inter_subset_left
      exact (interior_mono h_subset) hx
    have hUx : x ∈ U := by
      have : x ∈ A ∩ U := interior_subset hx
      exact this.2
    exact And.intro hA hUx
  · intro x hx
    rcases hx with ⟨hIntA, hUx⟩
    -- The set `interior A ∩ U` is open
    have h_open : IsOpen (interior A ∩ U) := isOpen_interior.inter hU
    -- and contained in `A ∩ U`
    have h_subset : (interior A ∩ U) ⊆ (A ∩ U) := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- Hence it is contained in the interior of `A ∩ U`
    have h_interior :
        interior A ∩ U ⊆ interior (A ∩ U) :=
      interior_maximal h_subset h_open
    exact h_interior ⟨hIntA, hUx⟩