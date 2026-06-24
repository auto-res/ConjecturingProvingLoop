

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P3 (X := X) A := by
  intro hP2
  apply Set.Subset.trans hP2
  have hclosure : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  exact interior_mono hclosure