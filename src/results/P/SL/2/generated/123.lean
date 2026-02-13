

theorem Topology.interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP1 x hx_int_cl
  -- First inclusion: `interior (closure A) ⊆ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := interior_subset hx_int_cl
  -- Second inclusion provided by `P1 A`: `closure A ⊆ closure (interior A)`.
  have h_cl_subset :
      (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  exact h_cl_subset hx_clA