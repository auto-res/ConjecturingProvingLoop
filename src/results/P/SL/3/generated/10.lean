

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this