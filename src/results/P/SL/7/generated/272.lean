

theorem Topology.P2_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    A ⊆ interior (closure (interior (closure A))) := by
  intro x hxA
  -- From `P2` we have membership in `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Monotonicity upgrades this to the desired larger set.
  have hMono :
      interior (closure (interior A)) ⊆
        interior (closure (interior (closure A))) := by
    apply interior_mono
    -- Show the corresponding inclusion for the closures.
    have hSub :
        closure (interior A) ⊆ closure (interior (closure A)) := by
      apply closure_mono
      exact Topology.interior_subset_interiorClosure (A := A)
    exact hSub
  exact hMono hxInt