

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  intro x hx_closureA
  -- First, from `P1 A`, we know `closure A ⊆ closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) := by
    have hsubset : closure A ⊆ closure (interior A) :=
      Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
    exact hsubset hx_closureA
  -- Next, `interior A ⊆ interior (closure A)`; taking closures preserves inclusion.
  have hsubset₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have hInt : (interior A : Set X) ⊆ interior (closure A) := by
      -- `A ⊆ closure A`, hence the same holds for interiors.
      have hIncl : (A : Set X) ⊆ closure A := subset_closure
      exact interior_mono hIncl
    exact closure_mono hInt
  -- Combining the two inclusions yields the desired membership.
  exact hsubset₂ hx₁