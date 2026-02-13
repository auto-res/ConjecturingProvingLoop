

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P3 A) : Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  intro x hx
  exact
    (interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior)
      hx