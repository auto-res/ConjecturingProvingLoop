

theorem Topology.P1_iff_closure_eq_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) := by
  constructor
  · intro hP1
    have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
      -- Take closure on both sides of the inclusion provided by hP1
      have := closure_mono hP1
      simpa using this
    have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact Set.Subset.antisymm h₁ h₂
  · intro h_eq
    dsimp [Topology.P1]
    intro x hxA
    have : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    simpa [h_eq] using this