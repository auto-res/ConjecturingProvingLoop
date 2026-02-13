

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : A ∩ B ⊆ A)) hx
    have hxAB : x ∈ (A ∩ B) := interior_subset hx
    exact And.intro hxA hxAB.2
  · -- `⊇` direction
    intro x hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- The set `interior A ∩ B` is an open neighborhood of `x`
    have hOpen : IsOpen (interior A ∩ B) :=
      (isOpen_interior.inter hB)
    have hSubset : interior A ∩ B ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- By the characterization of the interior, `x` belongs to `interior (A ∩ B)`
    exact interior_maximal hSubset hOpen (And.intro hxIntA hxB)