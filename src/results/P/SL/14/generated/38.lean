

theorem Topology.dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- Since `A` is dense, its closure is the whole space.
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the interior of this closure is also the whole space.
  have : (x : X) ∈ interior (closure A) := by
    simpa [hclosure] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact this)
  exact this