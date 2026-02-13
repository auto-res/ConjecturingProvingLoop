

theorem Topology.interior_closure_interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure (interior (closure A))) := by
  -- Step 1: `interior A` is contained in `interior (closure A)`.
  have hInt : (interior A : Set X) ⊆ interior (closure A) := by
    have hSub : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono hSub
  -- Step 2: taking closures preserves inclusions.
  have hCl : (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hInt
  -- Step 3: taking interiors preserves inclusions once more.
  exact interior_mono hCl