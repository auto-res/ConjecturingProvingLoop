

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := interior A) := by
  dsimp [Topology.P3]
  intro x hx
  have hsubset : interior A ⊆ closure (interior A) := subset_closure
  have hIsOpen : IsOpen (interior A) := isOpen_interior
  have hInc : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal hsubset hIsOpen
  exact hInc hx