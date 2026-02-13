

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (A : Set X) = Set.univ) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hx
  have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hA, interior_univ]
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int] using hx_univ