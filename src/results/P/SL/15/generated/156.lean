

theorem interior_dense_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  simpa using (dense_iff_closure_eq (s := interior A))