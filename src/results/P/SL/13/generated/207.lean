

theorem Topology.closure_inter_closureInterior_eq_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)) ∩ closure (interior A) = closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hx₁ : (x : X) ∈ closure (A : Set X) :=
      (Topology.closure_interior_subset_closure (X := X) (A := A)) hx
    exact And.intro hx₁ hx