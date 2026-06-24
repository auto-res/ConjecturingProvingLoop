

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P3 A := by
  intro hA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    intro x hx
    have hcl : closure (interior A) ⊆ closure A := by
      have hIA : interior A ⊆ (A : Set X) := interior_subset
      exact closure_mono hIA
    exact interior_mono hcl hx
  exact subset_trans hA hsubset