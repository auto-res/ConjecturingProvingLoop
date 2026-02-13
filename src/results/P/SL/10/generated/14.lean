

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure A = closure (interior A) := by
  intro hA
  apply Set.Subset.antisymm
  ·
    have : closure A ⊆ closure (interior A) :=
      closure_minimal hA isClosed_closure
    exact this
  ·
    exact closure_mono interior_subset