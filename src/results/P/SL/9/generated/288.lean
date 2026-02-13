

theorem Topology.P1_of_boundary_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h : closure (A : Set X) \ interior A ⊆ closure (interior A)) :
    Topology.P1 (A := A) := by
  dsimp [Topology.P1] at *
  intro x hxA
  by_cases hxInt : x ∈ interior A
  · -- If `x` is in the interior of `A`, it is certainly in the closure of the interior.
    exact subset_closure hxInt
  · -- Otherwise, `x` lies on the boundary, which is assumed to be contained
    -- in `closure (interior A)`.
    have hx_boundary : x ∈ closure (A : Set X) \ interior A := by
      have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
      exact ⟨hx_closure, hxInt⟩
    exact h hx_boundary