

theorem exists_P3_open_dense {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ P3 U ∧ closure U = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact P3_univ (X := X)
  · simpa [closure_univ]

theorem P3_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A ⊆ interior (closure A)) : P3 A := by
  intro x hxA
  by_cases h_int : x ∈ interior A
  ·
    -- `x` already lies in `interior A`, hence in `interior (closure A)`
    have h_subset :
        (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact h_subset h_int
  ·
    -- Otherwise, `x` is on the frontier of `A`
    have hx_frontier : x ∈ frontier A := by
      have hx_cl : (x : X) ∈ closure A := subset_closure hxA
      exact ⟨hx_cl, h_int⟩
    -- Apply the hypothesis on the frontier
    exact h hx_frontier

theorem exists_P2_open_dense {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ P2 U ∧ closure U = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact P2_univ (X := X)
  · simpa [closure_univ]