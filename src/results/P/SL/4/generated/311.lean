

theorem interior_closure_diff_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  -- `hx` gives membership in the interior of `closure A`
  -- and non-membership in `closure (interior A)`.
  have hxIntCl : x ∈ interior (closure A) := hx.1
  have hxNotClInt : x ∉ closure (interior A) := hx.2
  -- Any point of `interior (closure A)` lies in `closure A`.
  have hxClA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntCl
  -- Show that `x` is not in `interior A`; otherwise we contradict `hxNotClInt`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    -- `interior A` is contained in its closure, contradicting `hxNotClInt`.
    have : x ∈ closure (interior A) := subset_closure hxIntA
    exact hxNotClInt this
  -- Assemble the two conditions defining `frontier A`.
  exact And.intro hxClA hxNotIntA