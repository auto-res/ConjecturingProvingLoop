

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro h
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h_int : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_subset
  exact Set.Subset.trans h h_int