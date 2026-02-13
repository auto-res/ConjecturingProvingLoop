

theorem Topology.subset_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure A)) := by
  intro hP1
  -- Step 1: from `P1`, we have `A ⊆ closure (interior A)`.
  have h₁ : (A : Set X) ⊆ closure (interior A) := hP1
  -- Step 2: `interior A ⊆ interior (closure A)` by monotonicity.
  have hInt : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Step 3: taking closures preserves the inclusion.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hInt
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂