

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (h hx)

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  intro x hx
  exact (interior_mono (closure_mono interior_subset)) (h hx)