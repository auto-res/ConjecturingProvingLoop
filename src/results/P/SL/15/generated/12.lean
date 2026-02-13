

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    -- `closure (interior A)` is contained in `closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- `closure A` is contained in `closure (interior A)`
    have h₂ : closure A ⊆ closure (interior A) := by
      have h_sub : A ⊆ closure (interior A) := hP1
      have : closure A ⊆ closure (closure (interior A)) := closure_mono h_sub
      simpa using this
    exact Set.Subset.antisymm h₂ h₁
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have hx_closure : x ∈ closure A := subset_closure hx
    simpa [hEq] using hx_closure