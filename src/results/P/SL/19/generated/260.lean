

theorem Topology.interior_inter_interior_closure_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (closure A) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hx' : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hx
    exact And.intro hx hx'