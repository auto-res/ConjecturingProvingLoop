

theorem interior_diff_closureInterior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) \ closure (interior A) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    -- `x` lies in `interior A`.
    have hxInt : x ∈ interior (A : Set X) := hx.1
    -- `interior A ⊆ closure (interior A)`.
    have hsubset : interior (A : Set X) ⊆ closure (interior A) :=
      subset_closure
    -- Hence `x ∈ closure (interior A)`.
    have hxCl : x ∈ closure (interior A) := hsubset hxInt
    -- Contradiction with `x ∉ closure (interior A)`.
    exact (hx.2 hxCl).elim
  · intro hx
    -- No element lies in the empty set.
    cases hx