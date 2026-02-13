

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  -- First we show  `interior (A ∩ B) ⊆ interior A ∩ B`.
  have h₁ : interior (A ∩ B) ⊆ interior A ∩ B := by
    intro x hx
    -- `x` belongs to the interior of `A`, because `A ∩ B ⊆ A`.
    have hxA : x ∈ interior A := by
      have hsub : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact (interior_mono hsub) hx
    -- `x` belongs to the interior of `B`, because `A ∩ B ⊆ B`.
    have hxB_int : x ∈ interior B := by
      have hsub : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono hsub) hx
    -- Since `B` is open, `interior B = B`.
    have hxB : x ∈ B := by
      simpa [hB.interior_eq] using hxB_int
    exact And.intro hxA hxB
  -- Now we prove the reverse inclusion `interior A ∩ B ⊆ interior (A ∩ B)`.
  have h₂ : interior A ∩ B ⊆ interior (A ∩ B) := by
    intro x hx
    have hxA : x ∈ interior A := hx.1
    have hxB : x ∈ B := hx.2
    -- The set `interior A ∩ B` is open since it is the intersection of two open sets.
    have hOpen : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    -- Moreover, it is contained in `A ∩ B`.
    have hsubset : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- Therefore every point of `interior A ∩ B` lies in `interior (A ∩ B)`.
    have hIntSubset :
        (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal hsubset hOpen
    exact hIntSubset (And.intro hxA hxB)
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂