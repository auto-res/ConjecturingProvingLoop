

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  -- Unfold the definition of `P1`
  unfold Topology.P1 at *
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`
  have h₁ : closure A ⊆ closure (interior A) := by
    -- `closure_mono` applied to `hP1`
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- First, `interior A ⊆ interior (closure A)`
    have h_int : interior A ⊆ interior (closure A) := by
      apply interior_mono
      exact subset_closure
    -- Taking closures preserves the inclusion
    exact closure_mono h_int
  -- Combine the two inclusions to get the desired subset relation
  have h_subset : closure A ⊆ closure (interior (closure A)) :=
    Set.Subset.trans h₁ h₂
  exact h_subset hx