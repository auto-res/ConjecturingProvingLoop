

theorem interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro x hx
  have hx_cl : x ∈ closure (A : Set X) := interior_subset hx
  have hsubset : closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P1_closure_subset (X := X) (A := A) hP1
  exact hsubset hx_cl