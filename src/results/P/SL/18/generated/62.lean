

theorem dense_iff_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ closure (A : Set X) = Set.univ := by
  classical
  constructor
  · intro hDense
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      exact hDense x
  · intro hEq
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hEq] using this