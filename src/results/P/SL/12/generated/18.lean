

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  have h :
      interior (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  simpa [interior_interior] using h