

theorem interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- Step 1: `x` lies in `interior (closure A)` because interiors are monotone
  have hxIntClosureA : x ∈ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A) hxIntA
  -- Step 2: every point of `interior (closure A)` lies in
  --         `closure (interior (closure A))`
  have hIncl : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro y hy
    exact subset_closure hy
  -- Finish by combining the two facts
  exact hIncl hxIntClosureA