

theorem Topology.P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hx
  have hsubset : A ⊆ closure A := subset_closure
  have hInc : A ⊆ interior (closure A) := interior_maximal hsubset hA
  exact hInc hx