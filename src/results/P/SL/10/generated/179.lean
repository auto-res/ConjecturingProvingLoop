

theorem Topology.interior_inter_eq_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B)` is contained in each interior separately.
    exact Topology.interior_inter_subset (X := X) (A := A) (B := B)
  · -- The reverse inclusion: an open set inside `A ∩ B` yields membership in the interior.
    intro x hx
    -- `interior A ∩ interior B` is open.
    have h_open : IsOpen (interior A ∩ interior B) :=
      isOpen_interior.inter isOpen_interior
    -- It sits inside `A ∩ B`.
    have h_subset : interior A ∩ interior B ⊆ (A ∩ B) := by
      intro y hy
      exact And.intro (interior_subset hy.1) (interior_subset hy.2)
    -- Hence its points belong to `interior (A ∩ B)`.
    exact (interior_maximal h_subset h_open) hx