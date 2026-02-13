

theorem P1_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = closure (interior A)) :
    Topology.P1 A := by
  have hSubset : A ⊆ closure (interior A) := by
    simpa [h] using (subset_closure : A ⊆ closure A)
  exact hSubset