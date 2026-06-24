

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P1 (X := X) A :=
by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ closure (interior A) := (interior_subset) hx
  exact this