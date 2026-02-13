

theorem interior_inter_eq_of_isOpen_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = interior (A : Set X) ∩ B := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B) ⊆ interior A ∩ B`
    intro x hx
    have hAB : (x : X) ∈ (A ∩ B : Set X) := interior_subset hx
    -- `x` belongs to `interior A`
    have hIntA : (x : X) ∈ interior (A : Set X) := by
      have h_subset : (A ∩ B : Set X) ⊆ (A : Set X) := Set.inter_subset_left
      exact (interior_mono h_subset) hx
    exact And.intro hIntA hAB.2
  · -- `interior A ∩ B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hIntA, hBx⟩
    -- The open set `interior A ∩ B` contains `x`
    have hOpen : IsOpen (interior (A : Set X) ∩ B) :=
      isOpen_interior.inter hB
    have hxOpen : (x : X) ∈ interior (A : Set X) ∩ B :=
      And.intro hIntA hBx
    have hxIntOpen : (x : X) ∈ interior (interior (A : Set X) ∩ B) := by
      simpa [hOpen.interior_eq] using hxOpen
    -- `interior A ∩ B ⊆ A ∩ B`
    have h_subset : (interior (A : Set X) ∩ B) ⊆ (A ∩ B : Set X) := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    exact (interior_mono h_subset) hxIntOpen