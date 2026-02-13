

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have hclosure :
        closure (interior (closure (interior A))) ⊆ closure (closure (interior A)) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure
  ·
    -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      -- Apply monotonicity of `interior` to the inclusion `interior A ⊆ closure (interior A)`.
      have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      simpa [interior_interior] using interior_mono this
    have hclosure :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono hsubset
    exact hclosure