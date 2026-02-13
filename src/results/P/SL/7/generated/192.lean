

theorem Topology.P3_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A ⊆ closure (interior (closure A)) := by
  intro hP3
  -- `P3` yields the inclusion `A ⊆ interior (closure A)`.
  have h₁ : (A : Set X) ⊆ interior (closure A) := hP3
  -- The interior of any set is contained in its closure.
  have h₂ : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro x hx
    exact subset_closure hx
  -- Transitivity of inclusions gives the result.
  exact Set.Subset.trans h₁ h₂