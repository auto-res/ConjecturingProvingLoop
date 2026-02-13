

theorem Topology.P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) := by
  dsimp [Topology.P1]
  intro x hx
  have hcl : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using hcl