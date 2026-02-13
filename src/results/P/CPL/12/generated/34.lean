

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior (A : Set X)) = closure A := by
  constructor
  · intro hP1
    exact closure_interior_eq_closure_of_P1 (A := A) hP1
  · intro hEq
    exact P1_of_closure_interior_eq_closure (A := A) hEq

theorem P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P2 A := by
  intro hDense
  have hEq : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  exact P2_of_dense_interior (A := A) hEq

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense A → P3 A := by
  intro hDense
  simpa using P3_of_dense_closure (A := A) hDense.closure_eq