

theorem exists_closed_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, IsClosed A ∧ Topology.P3 (X:=X) A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_⟩
  simpa using (Topology.P3_univ (X := X))

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hd : Dense A) : Topology.P1 (X:=X) A := by
  -- `A` is both closed and dense, hence it is the whole space
  have hAU : (A : Set X) = (Set.univ : Set X) := by
    simpa [hA.closure_eq] using hd.closure_eq
  -- Unfold the definition of `P1` and solve by `simp`
  unfold Topology.P1
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hAU, interior_univ, closure_univ] using this