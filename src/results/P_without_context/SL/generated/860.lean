

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A :=
by
  intro h
  exact h.trans interior_subset