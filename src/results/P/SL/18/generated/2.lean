

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have : closure A ⊆ closure (closure (interior A)) := by
      exact closure_mono h
    simpa [closure_closure] using this
  ·
    exact closure_mono interior_subset