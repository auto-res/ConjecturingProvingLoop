

theorem Topology.interior_of_open_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : IsOpen (closure (interior (A : Set X)))) :
    interior (closure (interior (A : Set X))) = closure (interior A) := by
  simpa [h.interior_eq]