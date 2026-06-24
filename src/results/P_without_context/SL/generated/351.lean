

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h_closure
  exact Set.Subset.trans h h_subset