

theorem P3_iff_dense_union_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ closure A = closure (interior (closure A)) ∧ A ⊆ interior (closure A) := by
  constructor
  · intro hP3
    exact ⟨closure_eq_of_P3 (A := A) hP3, hP3⟩
  · rintro ⟨_, h_subset⟩
    exact h_subset

theorem P1_iff_dense_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ closure A = closure (interior A) := by
  simpa [eq_comm] using (P1_iff_closure_interior_eq (A := A))