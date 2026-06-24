

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P3 A := by
  intro hA
  have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have : interior A ⊆ A := interior_subset
    exact closure_mono this
  exact hA.trans h_sub