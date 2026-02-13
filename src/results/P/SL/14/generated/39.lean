

theorem Topology.closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  -- First inclusion: `closure (interior (closure (interior A))) ⊆ closure (interior A)`.
  have h₁ : closure (interior (closure (interior A))) ⊆ closure (interior A) := by
    have h₁' : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    exact closure_minimal h₁' isClosed_closure
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure (interior A)))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    have h_temp : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have h₂' : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using interior_mono h_temp
    exact closure_mono h₂'
  exact Set.Subset.antisymm h₁ h₂