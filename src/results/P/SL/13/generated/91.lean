

theorem Topology.interior_closure_interior_eq_interior_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  · -- First inclusion: `interior (closure (interior A)) ⊆ interior A`.
    have h_subset : closure (interior A) ⊆ (A : Set X) := by
      -- `interior A ⊆ A`, hence their closures are related.
      have h_int : interior A ⊆ (A : Set X) := interior_subset
      have h_cl : closure (interior A) ⊆ closure (A : Set X) := closure_mono h_int
      simpa [hA_closed.closure_eq] using h_cl
    -- Monotonicity of `interior`.
    exact interior_mono h_subset
  · -- Second inclusion: `interior A ⊆ interior (closure (interior A))`.
    -- `interior A` is open and contained in `closure (interior A)`.
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have h_open : IsOpen (interior A) := isOpen_interior
    exact interior_maximal h_subset h_open