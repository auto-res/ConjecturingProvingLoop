

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P3 A := by
  intro hP2
  have h_int : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_cl : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono h_cl
  exact fun x hx => h_int (hP2 hx)