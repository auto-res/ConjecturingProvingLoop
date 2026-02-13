

theorem Topology.interior_closure_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure A))) ⊆ interior (closure (closure A)) :=
      Topology.interior_closure_interior_subset_interior_closure (X:=X) (A:=closure A)
    simpa [closure_closure] using h
  ·
    intro x hx
    have hx_inner : (x : X) ∈ interior (interior (closure A)) := by
      simpa [interior_interior] using hx
    have h_subset : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro y hy
      exact subset_closure hy
    have h_inc :
        interior (interior (closure A)) ⊆ interior (closure (interior (closure A))) :=
      interior_mono h_subset
    exact h_inc hx_inner