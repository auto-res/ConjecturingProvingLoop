

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (A := A) ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    have h₂ : closure A ⊆ closure (interior A) := by
      have h : (A : Set X) ⊆ closure (interior A) := hP1
      simpa using (closure_mono h)
    exact subset_antisymm h₁ h₂
  · intro h_eq
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    simpa [h_eq] using hx_cl