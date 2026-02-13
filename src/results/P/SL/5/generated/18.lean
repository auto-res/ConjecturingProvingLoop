

theorem closure_interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have hsubset : (A : Set X) ⊆ closure A := subset_closure
  exact Topology.closure_interior_mono hsubset