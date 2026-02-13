

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (X:=X) (interior A) := by
  exact
    P3_of_P2 (X := X) (A := interior A) (P2_interior (X := X) (A := A))

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 (X:=X) A) : closure (interior A) = closure (interior (closure A)) := by
  -- Obtain `P1` and `P3` from the given `P2`
  have hP1 : P1 (X := X) A := P1_of_P2 (A := A) h
  have hP3 : P3 (X := X) A := P3_of_P2 (A := A) h
  -- Translate these properties into equalities of closures
  have h1 : closure (interior A) = closure A :=
    (P1_iff_closure_interior_subset (A := A)).1 hP1
  have h2 : closure A = closure (interior (closure A)) :=
    closure_eq_of_P3 (A := A) hP3
  -- Chain the equalities
  simpa using h1.trans h2

theorem exists_dense_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Dense A ∧ P3 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using dense_univ
  · simpa using (P3_univ (X := X))