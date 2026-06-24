

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A :=
by
  intro h
  dsimp [P2, P1] at *
  intro x hx
  exact interior_subset (h hx)