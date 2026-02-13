

theorem Topology.interior_inter_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  -- First inclusion: `interior (A ∩ B) ⊆ interior A ∩ B`.
  have h₁ : interior (A ∩ B : Set X) ⊆ interior A ∩ B := by
    have h := Topology.interior_inter_subset (X := X) (A := A) (B := B)
    simpa [hB.interior_eq] using h
  -- Second inclusion: `interior A ∩ B ⊆ interior (A ∩ B)`.
  have h₂ : interior A ∩ B ⊆ interior (A ∩ B) := by
    intro x hx
    rcases hx with ⟨hx_intA, hxB⟩
    -- The set `interior A ∩ B` is open and contains `x`.
    have h_open : IsOpen (interior A ∩ B) :=
      IsOpen.inter isOpen_interior hB
    -- This set is contained in `A ∩ B`.
    have h_subset : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy; exact ⟨interior_subset hy.1, hy.2⟩
    -- Hence it lies in the interior of `A ∩ B`.
    have h_max : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal h_subset h_open
    exact h_max ⟨hx_intA, hxB⟩
  -- Combine the inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂