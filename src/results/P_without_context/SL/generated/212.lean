

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    intro x hx
    have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hcl hx
  exact subset_trans hA hsubset