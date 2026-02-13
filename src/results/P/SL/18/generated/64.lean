

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x _hxA
  -- `Dense` gives `closure A = univ`.
  have hCl : closure (A : Set X) = Set.univ :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  -- Hence `interior (closure A)` is `univ`, and the goal is immediate.
  have : x ∈ interior (closure (A : Set X)) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hCl, interior_univ] using this
  exact this