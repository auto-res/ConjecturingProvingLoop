

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hA
  have h₁ : closure (interior A) ⊆ closure A := by
    have : interior A ⊆ A := interior_subset
    exact closure_mono this
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact subset_trans hA h₂