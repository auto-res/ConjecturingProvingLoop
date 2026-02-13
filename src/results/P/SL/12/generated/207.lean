

theorem Topology.open_subset_closure_implies_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen (U : Set X)) (h_subset : (U : Set X) ⊆ closure (A : Set X)) :
    (U : Set X) ⊆ interior (closure A) := by
  exact interior_maximal h_subset hU