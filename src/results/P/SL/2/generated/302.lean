

theorem Topology.closure_diff_interior_compl_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) =
      closure (Aᶜ : Set X) \ interior (Aᶜ : Set X) := by
  calc
    closure (A : Set X) \ interior (A : Set X)
        = frontier (A : Set X) := rfl
    _ = frontier ((Aᶜ) : Set X) :=
      (Topology.frontier_compl (A := A)).symm
    _ = closure (Aᶜ : Set X) \ interior (Aᶜ : Set X) := rfl