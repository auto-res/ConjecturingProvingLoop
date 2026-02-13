

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P1 A := by
  intro hInt
  -- Since `interior A = univ`, its closure is also `univ`.
  have h_closure : (closure (interior A) : Set X) = Set.univ := by
    simpa [hInt, closure_univ]
  -- Provide the required inclusion.
  have h_subset : (A : Set X) ⊆ closure (interior A) := by
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [h_closure] using this
  simpa [P1] using h_subset

theorem exists_P3_closed_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsClosed B ∧ P3 B := by
  refine ⟨Set.univ, ?_, isClosed_univ, P3_univ⟩
  intro x hx
  trivial