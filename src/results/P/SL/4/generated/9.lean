

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A = closure (interior A) := by
  intro hP1
  apply subset_antisymm
  · have : closure A ⊆ closure (closure (interior A)) := by
      exact closure_mono hP1
    simpa using this
  · exact closure_mono interior_subset