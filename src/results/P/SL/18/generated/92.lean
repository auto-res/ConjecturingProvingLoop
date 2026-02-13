

theorem closure_subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure A ⊆ closure (interior A) := by
  simpa [closure_closure] using (closure_mono hP1)