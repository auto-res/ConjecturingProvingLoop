

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA.closure_eq]
  have hsub : (A : Set X) ⊆ interior (closure A) := by
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hInt] using this
  simpa using hsub