

theorem Topology.closure_interior_closure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure A)) ⊆ closure A`
    exact Topology.closure_interior_closure_subset_closure (A := A)
  · -- `closure A ⊆ closure (interior (closure A))`
    have hSub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : A ⊆ closure A) hA
    exact (closure_mono hSub)