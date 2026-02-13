

theorem Topology.closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- First inclusion: `closure (interior (A ∩ B)) ⊆ closure (interior A)`
  have hA : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
    -- Since `A ∩ B ⊆ A`, we get `interior (A ∩ B) ⊆ interior A`.
    have hinner : interior (A ∩ B) ⊆ interior A := by
      have hsubset : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact interior_mono hsubset
    -- Taking closures preserves inclusion.
    exact closure_mono hinner
  -- Second inclusion: `closure (interior (A ∩ B)) ⊆ closure (interior B)`
  have hB : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
    -- Since `A ∩ B ⊆ B`, we get `interior (A ∩ B) ⊆ interior B`.
    have hinner : interior (A ∩ B) ⊆ interior B := by
      have hsubset : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact interior_mono hsubset
    -- Taking closures preserves inclusion.
    exact closure_mono hinner
  exact And.intro (hA hx) (hB hx)