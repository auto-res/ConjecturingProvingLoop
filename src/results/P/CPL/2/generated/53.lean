

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hDense : Dense A) : Topology.P2 (X:=X) A := by
  -- Since `A` is closed and dense, it must be the whole space
  have hAU : (A : Set X) = (Set.univ : Set X) := by
    have : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
    simpa [hA.closure_eq] using this
  -- Conclude using the already proved `P2` for `univ`
  simpa [hAU] using (P2_univ (X := X))

theorem exists_open_dense_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P1 (X:=X) U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, ?_⟩
  simpa using (P1_univ (X := X))