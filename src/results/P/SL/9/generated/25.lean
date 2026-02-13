

theorem Topology.P1_iff_closureInterior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    -- `closure (interior A)` is always contained in `closure A`.
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- From `P1`, we also have the reverse inclusion after taking closures.
    have h₂ : closure A ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      simpa [closure_closure] using closure_mono hA
    exact subset_antisymm h₁ h₂
  · intro hEq
    dsimp [Topology.P1]
    intro x hxA
    have hx_closure : x ∈ closure A := Set.subset_closure hxA
    simpa [hEq] using hx_closure