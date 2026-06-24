

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h0 : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono h0
  exact fun x hx => h1 (hP2 hx)