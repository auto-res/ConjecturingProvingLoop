

theorem open_satisfies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  have h : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono subset_closure
  simpa [interior_interior, hA.interior_eq] using h