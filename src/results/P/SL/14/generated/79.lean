

theorem Topology.closureInteriorClosure_eq_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure (interior (closure A)) = closure (interior A) := by
  -- First inclusion: `closure (interior (closure A)) ⊆ closure (interior A)`.
  have h_closureA_subset : (closure A : Set X) ⊆ closure (interior A) := by
    -- From `P1`, we know `A ⊆ closure (interior A)`.  Taking closures yields
    -- `closure A ⊆ closure (closure (interior A)) = closure (interior A)`.
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono (hP1 : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using this
  have h_int_subset : (interior (closure A) : Set X) ⊆ closure (interior A) :=
    Set.Subset.trans
      (interior_subset : interior (closure A) ⊆ closure A)
      h_closureA_subset
  have h₁ : closure (interior (closure A)) ⊆ closure (interior A) :=
    closure_minimal h_int_subset isClosed_closure
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closureInterior_subset_closureInteriorClosure (X := X) (A := A)
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂