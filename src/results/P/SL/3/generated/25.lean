

theorem closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  intro hA
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior (closure A))`
    have h₁ : (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
      have hA' : (A : Set X) ⊆ interior (closure (A : Set X)) := hA
      exact Set.Subset.trans hA' subset_closure
    exact closure_minimal h₁ isClosed_closure
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h₂ : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
      interior_subset (s := closure (A : Set X))
    simpa [closure_closure] using closure_mono h₂