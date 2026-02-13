

theorem Topology.closure_subset_closure_left_of_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ closure (B : Set X)) :
    closure (A : Set X) ⊆ closure B := by
  simpa [closure_closure] using closure_mono h