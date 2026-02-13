

theorem Topology.closure_interior_inter_frontier_closure_eq_closure_interior_diff_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ frontier (closure A) =
      closure (interior A) \ interior (closure A) := by
  -- First, rewrite the frontier of a closed set.
  have hFront :
      frontier (closure A) =
        closure A \ interior (closure A) := by
    simp [frontier, closure_closure]
  -- We now identify the desired equality by set‐extensionality.
  ext x
  constructor
  · intro hx
    -- Decompose the membership in the intersection.
    rcases hx with ⟨hxClosInt, hxDiff⟩
    -- `hxDiff` witnesses `x ∈ closure A ∧ x ∉ interior (closure A)`.
    exact And.intro hxClosInt hxDiff.2
  · intro hx
    rcases hx with ⟨hxClosInt, hxNotIntClos⟩
    -- From `x ∈ closure (interior A)` we infer `x ∈ closure A`.
    have hxClosA : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hxClosInt
    -- Assemble the data to obtain membership in the original intersection.
    have hxDiff : x ∈ closure A \ interior (closure A) :=
      And.intro hxClosA hxNotIntClos
    -- Conclude the required membership.
    have : x ∈ closure (interior A) ∩ (closure A \ interior (closure A)) :=
      And.intro hxClosInt hxDiff
    -- Rewrite back using `hFront`.
    simpa [hFront] using this