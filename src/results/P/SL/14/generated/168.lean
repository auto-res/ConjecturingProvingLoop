

theorem Topology.interior_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  -- First inclusion: `interior (A ∩ B) ⊆ A ∩ interior B`.
  have h₁ : interior (A ∩ B : Set X) ⊆ A ∩ interior B := by
    -- Use the general inclusion and rewrite `interior A` using openness.
    have h := Topology.interior_inter_subset (X := X) (A := A) (B := B)
    simpa [hA.interior_eq] using h
  -- Second inclusion: `A ∩ interior B ⊆ interior (A ∩ B)`.
  have h₂ : A ∩ interior B ⊆ interior (A ∩ B) := by
    intro x hx
    rcases hx with ⟨hxA, hx_intB⟩
    -- The set `A ∩ interior B` is an open neighbourhood of `x`.
    have h_open : IsOpen (A ∩ interior B) :=
      IsOpen.inter hA isOpen_interior
    -- It is contained in `A ∩ B`.
    have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨hy.1, interior_subset hy.2⟩
    -- Hence it lies inside the interior of `A ∩ B`.
    have h_max :
        (A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal h_subset h_open
    exact h_max ⟨hxA, hx_intB⟩
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂