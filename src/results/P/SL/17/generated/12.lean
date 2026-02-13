

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Dense A) : Topology.P3 A := by
  unfold Topology.P3
  intro x hx
  have hclosure : closure A = (Set.univ : Set X) := hA.closure_eq
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hclosure] using interior_univ
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using this