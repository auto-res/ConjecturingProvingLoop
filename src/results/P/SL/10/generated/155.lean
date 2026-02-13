

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- `interior A` is open and included in its closure.
  have h_open : IsOpen (interior A) := isOpen_interior
  have h_subset : interior A ⊆ closure (interior A) := subset_closure
  -- Apply `interior_maximal` to obtain the desired inclusion.
  exact interior_maximal h_subset h_open