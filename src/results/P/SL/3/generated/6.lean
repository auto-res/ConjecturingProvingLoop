

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have h : A ⊆ interior (closure A) := by
    apply interior_maximal
    · exact subset_closure
    · exact hA
  simpa [hA.interior_eq] using h