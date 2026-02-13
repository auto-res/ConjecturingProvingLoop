

theorem isOpen_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X:=X) A := by
  dsimp [Topology.P1]
  intro x hx
  have h_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure h_int