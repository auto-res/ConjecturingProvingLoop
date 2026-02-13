

theorem interior_closure_interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  dsimp [Topology.P1]
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa [hOpen.interior_eq] using
    (subset_closure :
      interior (closure (interior A)) ⊆ closure (interior (closure (interior A))))