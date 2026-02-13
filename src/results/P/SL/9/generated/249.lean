

theorem Topology.interior_inter_closure_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∩ closure A) = interior A := by
  -- We prove the two inclusions separately.
  apply subset_antisymm
  · -- `interior (A ∩ closure A)` is contained in `interior A`
    have h_subset : (A ∩ closure A : Set X) ⊆ A := by
      intro x hx; exact hx.1
    exact interior_mono h_subset
  · -- `interior A` is open and contained in `A ∩ closure A`,
    -- hence it is contained in the interior of that set.
    have h_subset : (interior A : Set X) ⊆ A ∩ closure A := by
      intro x hx
      have hxA : x ∈ A := interior_subset hx
      have hx_cl : x ∈ closure A := subset_closure hxA
      exact ⟨hxA, hx_cl⟩
    have h_open : IsOpen (interior A) := isOpen_interior
    exact interior_maximal h_subset h_open