

theorem Topology.closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : (A : Set X) ⊆ closure A := subset_closure
  simpa using
    (Topology.closure_interior_mono (X := X) (A := A) (B := closure A) h)