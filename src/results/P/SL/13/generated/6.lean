

theorem Topology.dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Dense A) : Topology.P3 (X:=X) A := by
  dsimp [Topology.P3]
  intro x _
  have h_cl : closure A = (Set.univ : Set X) := hA.closure_eq
  simpa [h_cl, interior_univ]