

theorem Topology.interior_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx' : (x : X) ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hx
  exact subset_closure hx'