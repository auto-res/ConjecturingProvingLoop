

theorem Topology.P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  unfold Topology.P3
  intro x hx
  have hsubset : A ⊆ interior (closure A) := interior_maximal subset_closure hA
  exact hsubset hx