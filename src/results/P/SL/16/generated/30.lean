

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h : interior (closure (interior A)) ⊆ closure (interior A) := by
      simpa using (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
    have h' : closure (interior (closure (interior A))) ⊆
        closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using h'
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    have h' : closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h
    exact h'