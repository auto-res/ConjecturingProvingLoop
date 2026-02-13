

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P1 A := by
  intro hClosed hP3
  intro x hxA
  have hxIntClosure : x ∈ interior (closure A) := hP3 hxA
  have hClosureEq : closure A = A := hClosed.closure_eq
  have hxInt : x ∈ interior A := by
    simpa [hClosureEq] using hxIntClosure
  exact subset_closure hxInt

theorem P1_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → (P1 A ↔ P2 A) := by
  intro hDense
  constructor
  · intro hP1
    -- First, show that `closure (interior A) = univ`.
    have h_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      exact closure_minimal hA isClosed_closure
    have h_univ : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [hDense] using h_subset
    have h_closure_int_univ : closure (interior A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · exact h_univ
    -- With this equality, `P2 A` follows.
    have hP2 : P2 A := by
      intro x hxA
      have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [h_closure_int_univ, interior_univ] using hx_univ
    exact hP2
  · intro hP2
    exact (P2_subset_P1 (A := A)) hP2

theorem exists_P1_closed_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ IsClosed B ∧ P1 B := by
  refine ⟨Set.univ, ?_, isClosed_univ, P1_univ⟩
  intro x hx
  trivial