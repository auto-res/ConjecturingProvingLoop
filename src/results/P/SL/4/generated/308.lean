

theorem interior_closure_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) \ interior A ⊆ frontier A := by
  intro x hx
  -- Extract the two conditions from the set difference.
  have hxIntClosure : x ∈ interior (closure A) := hx.1
  have hxNotIntA : x ∉ interior A := hx.2
  -- Any point of `interior (closure A)` lies in `closure A`.
  have hxClosureA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClosure
  -- Combine the facts to obtain membership in the frontier.
  exact And.intro hxClosureA hxNotIntA