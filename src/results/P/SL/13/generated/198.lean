

theorem Topology.interior_closure_interiorClosure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆
      closure (interior (closure A)) := by
  intro x hx
  -- `interior S ⊆ S` for every set `S`, and `S ⊆ closure S`.
  -- Combining the two inclusions for `S = closure (interior (closure A))`
  -- yields the desired result.
  exact
    (interior_subset :
      interior (closure (interior (closure (A : Set X)))) ⊆
        closure (interior (closure A))) hx