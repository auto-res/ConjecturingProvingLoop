

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  -- `x` certainly belongs to the interior of `closure (interior A)` because that set is `⊤`.
  have hxInt : x ∈ interior (closure (interior A)) := by
    have : x ∈ (Set.univ : Set X) := Set.mem_univ x
    simpa [hDense, interior_univ] using this
  -- Monotonicity of `interior` and `closure` lets us upgrade the membership.
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset : interior A ⊆ A)
  exact hsubset hxInt