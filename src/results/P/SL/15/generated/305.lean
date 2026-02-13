

theorem interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `interior (closure A) = univ` implies `univ ⊆ closure A`
    have h₁ : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      -- From `hInt`, we know `x ∈ interior (closure A)`
      have hx : x ∈ interior (closure A) := by
        simpa [hInt] using (Set.mem_univ x)
      -- `interior (closure A)` is contained in `closure A`
      exact interior_subset hx
    -- The reverse inclusion is trivial
    have h₂ : (closure A : Set X) ⊆ (Set.univ : Set X) := by
      intro x _; trivial
    exact Set.Subset.antisymm h₂ h₁
  · intro hClos
    -- If `closure A = univ`, so is its interior
    simpa [hClos, interior_univ]