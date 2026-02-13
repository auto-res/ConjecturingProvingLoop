

theorem Topology.P3_implies_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A ⊆ closure (interior (closure A)) := by
  intro hP3
  exact closure_mono hP3