

theorem Topology.frontier_inter_interior_closure_eq_diff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ∩ interior (closure A) = interior (closure A) \ interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hFront, hIntClos⟩
    -- `hFront` gives both `x ∈ closure A` and `x ∉ interior A`;
    -- `hIntClos` is `x ∈ interior (closure A)`.
    exact ⟨hIntClos, hFront.2⟩
  · intro hx
    rcases hx with ⟨hIntClos, hNotIntA⟩
    -- From `x ∈ interior (closure A)` we deduce `x ∈ closure A`.
    have hClA : x ∈ closure A := interior_subset hIntClos
    -- Assemble the frontier membership.
    have hFront : x ∈ frontier A := And.intro hClA hNotIntA
    exact And.intro hFront hIntClos