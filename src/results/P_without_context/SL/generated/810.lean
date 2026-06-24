

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  exact interior_subset hx'