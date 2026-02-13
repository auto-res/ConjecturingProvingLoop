

theorem closure_eq_univ_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (A : Set X) = Set.univ) : P3 (X := X) A := by
  dsimp [P3]
  intro x hx
  -- acknowledge the assumption to avoid unused variable warnings
  have _ : x ∈ A := hx
  -- since `closure A = univ`, its interior is also `univ`
  have : x ∈ interior (closure (A : Set X)) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hA, interior_univ] using this
  exact this