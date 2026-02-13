

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    interior (U ∩ A) = U ∩ interior A := by
  apply Set.Subset.antisymm
  · -- `interior (U ∩ A) ⊆ U ∩ interior A`
    intro x hx
    have hxUA : x ∈ U ∩ A := interior_subset hx
    have hxU : x ∈ U := hxUA.1
    have hxIntA : x ∈ interior A := by
      have h_mono : interior (U ∩ A) ⊆ interior A :=
        interior_mono (Set.inter_subset_right : (U ∩ A) ⊆ A)
      exact h_mono hx
    exact And.intro hxU hxIntA
  · -- `U ∩ interior A ⊆ interior (U ∩ A)`
    intro x hx
    rcases hx with ⟨hxU, hxIntA⟩
    -- Define the open set `U ∩ interior A`.
    have h_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    -- It sits inside `U ∩ A`.
    have h_subset : (U ∩ interior A) ⊆ (U ∩ A) := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    -- Hence every point of `U ∩ interior A` belongs to the interior of `U ∩ A`.
    have h_into : (U ∩ interior A) ⊆ interior (U ∩ A) :=
      interior_maximal h_subset h_open
    exact h_into ⟨hxU, hxIntA⟩