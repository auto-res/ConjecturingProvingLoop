

theorem Topology.P1_of_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) → Topology.P1 A := by
  intro hIntEq
  intro x hxA
  -- Any point lies in `interior A` because `interior A = univ`.
  have hxInt : (x : X) ∈ interior (A : Set X) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hIntEq] using this
  -- Hence it lies in `closure (interior A)`.
  exact subset_closure hxInt