

theorem Topology.P2_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 (A := A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _
  -- Since `closure (interior A) = univ`, its interior is also `univ`.
  have hInt : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hDense, interior_univ]
  -- Any point `x` lies in `univ`, hence in the required interior.
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [hInt] using hx_univ