

theorem closure_subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro hP2
  have hEq := closure_eq_closure_interior_of_P2 (A := A) hP2
  simpa [hEq] using
    (subset_rfl : closure (A : Set X) ⊆ closure (A : Set X))