

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  -- Step 1: `x` lies in the closure of `interior A`.
  have hx_closure_int :
      x ∈ closure (interior A) :=
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) hx
  -- Step 2: `closure (interior A)` is contained in `closure A`.
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Combine the two facts to conclude.
  exact hsubset hx_closure_int