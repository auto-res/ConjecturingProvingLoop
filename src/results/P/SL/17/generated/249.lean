

theorem Topology.P1_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  -- Unfold the definition of `P1`.
  unfold Topology.P1
  -- Take an arbitrary point `x ∈ A`.
  intro x hxA
  -- Since `closure (interior A) = univ`, every point lies in it.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  -- Rewrite using the provided equality to get the desired membership.
  simpa [h] using this