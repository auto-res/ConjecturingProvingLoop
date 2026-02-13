

theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior (A : Set X)) ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hxA : (x : X) ∈ A :=
      (interior_subset : interior (A : Set X) ⊆ A) hx
    have hxCl : (x : X) ∈ closure A := subset_closure hxA
    exact ⟨hx, hxCl⟩