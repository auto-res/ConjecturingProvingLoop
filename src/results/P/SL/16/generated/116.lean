

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- First, upgrade the point from `interior A` to `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
  -- Any element of a set lies in the closure of that set.
  exact subset_closure hxIntCl