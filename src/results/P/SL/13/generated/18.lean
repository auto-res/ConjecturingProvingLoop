

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) = interior (closure (interior A)) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure (interior A)))) ⊆
          interior (closure (closure (interior A))) :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (interior A))
    simpa [closure_closure] using h
  ·
    intro x hx
    have hx_inner : (x : X) ∈ interior (interior (closure (interior A))) := by
      simpa [interior_interior] using hx
    have h_subset :
        interior (closure (interior A)) ⊆ closure (interior (closure (interior A))) := by
      intro y hy
      exact subset_closure hy
    have h_inc :
        interior (interior (closure (interior A))) ⊆
          interior (closure (interior (closure (interior A)))) :=
      interior_mono h_subset
    exact h_inc hx_inner