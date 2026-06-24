

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hA
  dsimp [P2] at hA
  dsimp [P1]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact h_subset hx'