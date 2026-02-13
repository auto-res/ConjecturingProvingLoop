

theorem Topology.interiorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h_closure_subset : closure (interior (closure A)) ⊆ closure A := by
      have h_int_subset : (interior (closure A) : Set X) ⊆ closure A :=
        interior_subset
      exact closure_minimal h_int_subset isClosed_closure
    exact interior_mono h_closure_subset
  ·
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    have h_subset : (interior (closure A) : Set X) ⊆
        closure (interior (closure A)) := subset_closure
    exact interior_maximal h_subset h_open