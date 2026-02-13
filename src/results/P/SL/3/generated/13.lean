

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → closure (A : Set X) = closure (interior (A : Set X)) := by
  intro hA
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior A)`
    have h : closure (A : Set X) ⊆ closure (interior A) := by
      apply closure_minimal hA
      exact isClosed_closure
    exact h
  · -- `closure (interior A) ⊆ closure A`
    have h : closure (interior (A : Set X)) ⊆ closure A := by
      exact closure_mono (interior_subset (s := A))
    exact h