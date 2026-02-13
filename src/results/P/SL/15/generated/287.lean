

theorem dense_implies_P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (interior (closure A)) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- `closure A` is the whole space because `A` is dense
  have h_closure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- hence its interior is also the whole space
  have h_int_closure : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
      using (congrArg id h_closure)
  -- rewrite the goal using these equalities
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int_closure, closure_univ, interior_univ] using this