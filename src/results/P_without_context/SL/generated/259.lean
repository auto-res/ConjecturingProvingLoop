

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  unfold P2 at hP2
  unfold P3
  have h1 : closure (interior A) ⊆ closure A := by
    apply closure_mono
    exact interior_subset
  have h2 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h1
  exact hP2.trans h2