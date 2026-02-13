

theorem Topology.P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  unfold Topology.P2
  intro x hx
  have hsubset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have : x ∈ interior (closure A) := hsubset hx
  simpa [hA.interior_eq] using this