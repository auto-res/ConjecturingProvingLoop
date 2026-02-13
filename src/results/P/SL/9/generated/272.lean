

theorem Topology.closureInterior_inter_frontier_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ frontier A = closure (interior A) \ interior A := by
  ext x
  constructor
  · intro hx
    -- `hx.1 : x ∈ closure (interior A)`
    -- `hx.2 : x ∈ frontier A = closure A \ interior A`
    exact ⟨hx.1, hx.2.2⟩
  · intro hx
    -- From `x ∈ closure (interior A)`,
    -- obtain `x ∈ closure A` via monotonicity of `closure`.
    have hx_closureA : x ∈ closure (A : Set X) := by
      have h_subset : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      exact h_subset hx.1
    -- Assemble the required membership in the intersection.
    exact ⟨hx.1, ⟨hx_closureA, hx.2⟩⟩