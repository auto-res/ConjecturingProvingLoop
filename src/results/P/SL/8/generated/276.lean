

theorem interior_inter_eq_inter_interior_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B) ⊆ interior A ∩ B`
    intro x hx
    have h₁ :
        x ∈ interior A ∧ x ∈ interior B :=
      (interior_inter_subset_inter_interior
        (X := X) (A := A) (B := B)) hx
    rcases h₁ with ⟨hIntA, hIntB⟩
    -- Since `B` is open, `interior B = B`.
    have hB_mem : x ∈ B := by
      simpa [hB.interior_eq] using hIntB
    exact And.intro hIntA hB_mem
  · -- `interior A ∩ B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- The set `V = interior A ∩ B` is an open neighbourhood of `x`
    -- contained in `A ∩ B`.
    have hV_open : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    have hV_subset : interior A ∩ B ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    have hxV : x ∈ interior A ∩ B := And.intro hxIntA hxB
    exact
      (Set.mem_interior).2 ⟨interior A ∩ B, hV_open, hV_subset, hxV⟩