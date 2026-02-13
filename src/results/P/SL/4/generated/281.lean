

theorem frontier_interior_eq_frontier_inter_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) = frontier A ∩ closure (interior A) := by
  ext x
  constructor
  · intro hx
    -- `hx` provides membership in the closure of `interior A`
    -- and non‐membership in its interior.
    have hClInt  : x ∈ closure (interior A) := hx.1
    have hNotInt : x ∉ interior A := by
      -- `hx.2 : x ∉ interior (interior A)`; rewrite with `interior_interior`.
      simpa [interior_interior] using hx.2
    -- Use monotonicity of `closure` to pass from
    -- `closure (interior A)` to `closure A`.
    have hClA : x ∈ closure A := by
      have hSub : closure (interior A) ⊆ closure A :=
        closure_interior_subset_closure (A := A)
      exact hSub hClInt
    -- Assemble the membership in `frontier A`.
    have hFrontA : x ∈ frontier A := And.intro hClA hNotInt
    exact And.intro hFrontA hClInt
  · intro hx
    -- Extract the two components of the intersection.
    have hFrontA : x ∈ frontier A := hx.1
    have hClInt  : x ∈ closure (interior A) := hx.2
    -- From `frontier A`, obtain `x ∉ interior A`.
    have hNotInt : x ∉ interior A := hFrontA.2
    -- Rewrite the non‐membership for `interior (interior A)`.
    have hNotIntInt : x ∉ interior (interior A) := by
      simpa [interior_interior] using hNotInt
    -- Conclude membership in `frontier (interior A)`.
    exact And.intro hClInt hNotIntInt