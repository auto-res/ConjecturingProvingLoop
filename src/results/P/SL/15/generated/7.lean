

theorem interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (closure (interior A)) ⊆ interior (closure A) := by
  open Set in
  have h_mono : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  exact interior_mono h_mono