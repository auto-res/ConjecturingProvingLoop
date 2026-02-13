

theorem closure_iInter_interior_subset {X ι : Type*} [TopologicalSpace X]
    {A : ι → Set X} :
    closure (⋂ i, interior (A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- For every `i`, show that `x` belongs to `closure (interior (A i))`.
  have hforall : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- The intersection is contained in each `interior (A i)`.
    have hsubset :
        (⋂ j, interior (A j)) ⊆ interior (A i) :=
      Set.iInter_subset (fun j : ι => interior (A j)) i
    -- Monotonicity of `closure` transfers membership.
    exact (closure_mono hsubset) hx
  -- Collect the witnesses into the intersection.
  exact Set.mem_iInter.2 hforall