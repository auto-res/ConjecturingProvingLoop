

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2 x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx