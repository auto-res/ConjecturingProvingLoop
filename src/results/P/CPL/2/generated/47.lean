

theorem P3_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior (closure A)) : Topology.P3 (X:=X) A := by
  -- Unfold the definition of `P3`
  unfold Topology.P3
  intro x hx
  -- `x` lies in the closure of `A`
  have hx_cl : (x : X) ∈ closure A := subset_closure hx
  -- Rewrite using the provided equality
  simpa using (h ▸ hx_cl)