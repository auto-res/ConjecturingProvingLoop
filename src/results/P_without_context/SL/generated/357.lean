

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2
  have h1 : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h2 : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono h1
  exact subset_trans hP2 h2