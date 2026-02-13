

theorem Topology.closure_diff_interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) →
      closure A \ interior (closure A) ⊆ closure (interior A) := by
  intro hP1
  intro x hx
  have hxClos : x ∈ closure A := hx.1
  have hSub : closure A ⊆ closure (interior A) :=
    Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  exact hSub hxClos