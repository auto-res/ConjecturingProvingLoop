

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    interior A ⊆ interior (closure (interior A)) := by
  dsimp [Topology.P2] at hP2
  intro x hxIntA
  exact hP2 ((interior_subset : interior A ⊆ A) hxIntA)