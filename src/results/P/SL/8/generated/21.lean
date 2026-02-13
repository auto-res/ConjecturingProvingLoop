

theorem P1_imp_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior A) = closure A := by
  dsimp [Topology.P1] at hP1
  apply Set.Subset.antisymm
  · -- `closure (interior A)` is contained in `closure A`
    have h : interior A ⊆ A := interior_subset
    exact closure_mono h
  · -- `closure A` is contained in `closure (interior A)`
    have h_cl : A ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h_cl
    simpa [closure_closure] using this