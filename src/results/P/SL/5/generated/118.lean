

theorem interior_closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  simpa using
    (Topology.interior_closure_inter_subset
        (X := X)
        (A := interior A)
        (B := interior B))