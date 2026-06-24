

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int