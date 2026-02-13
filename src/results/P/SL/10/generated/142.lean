

theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A ∩ closure A) = interior A := by
  apply Set.Subset.antisymm
  ·
    -- The interior of the intersection is contained in `A`, hence in `interior A`.
    have h : (A ∩ closure A) ⊆ A := Set.inter_subset_left
    exact interior_mono h
  ·
    -- `interior A` is an open subset of the intersection, so it lies in its interior.
    have h_subset : interior A ⊆ A ∩ closure A := by
      intro x hx
      have hxA : x ∈ A := interior_subset hx
      have hxCl : x ∈ closure A := subset_closure hxA
      exact And.intro hxA hxCl
    exact interior_maximal h_subset isOpen_interior