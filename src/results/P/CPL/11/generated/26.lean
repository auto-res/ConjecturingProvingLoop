

theorem P1_iff_dense_union_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A = closure (interior A) ∧ A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    have h_eq := (P1_iff_closure_interior_eq (A := A)).1 hP1
    exact ⟨h_eq.symm, hP1⟩
  · rintro ⟨_, h_subset⟩
    exact h_subset

theorem P2_of_P3_and_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_dense : closure (interior A) = closure A) : P2 A := by
  have h1 : P1 A := (P1_iff_closure_interior_eq (A := A)).2 h_dense
  exact P2_of_P1_and_P3 h1 h3