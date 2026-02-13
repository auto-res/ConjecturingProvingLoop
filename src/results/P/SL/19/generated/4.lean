

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → closure A = closure (interior A) := by
  intro hP1
  apply Set.Subset.antisymm
  · have h' : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h'
  · exact closure_mono interior_subset