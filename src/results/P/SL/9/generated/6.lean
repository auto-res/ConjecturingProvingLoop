

theorem Topology.P1_iff_closureInterior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (A := A) ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    have h₁ : A ⊆ closure (interior A) := hP1
    have h₂ : closure (interior A) ⊆ A := by
      have : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using this
    exact subset_antisymm h₂ h₁
  · intro hEq
    simpa [Topology.P1, hEq] using (subset_rfl : A ⊆ A)