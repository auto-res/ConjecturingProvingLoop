

theorem P3_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  -- `closure A` is the whole space thanks to density
  have h_closure_univ : (closure A : Set X) = (Set.univ : Set X) := by
    simpa [isClosed_closure.closure_eq] using hA.closure_eq
  -- hence its interior is also `univ`
  have h_interior_univ : (interior (closure A) : Set X) = Set.univ := by
    simpa [h_closure_univ, interior_univ]
  -- the inclusion is now obvious
  simpa [h_interior_univ]