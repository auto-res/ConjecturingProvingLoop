

theorem Topology.disjoint_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Disjoint (interior (A \ B : Set X)) (interior B) := by
  refine Set.disjoint_left.2 ?_
  intro x hx_diff hx_intB
  -- `x` lies in `A \ B`, hence it is not in `B`.
  have h_notB : (x : X) ∉ B := by
    have : (x : X) ∈ A \ B :=
      (interior_subset : interior (A \ B) ⊆ A \ B) hx_diff
    exact this.2
  -- But `x` also lies in `interior B`, which is contained in `B`.
  have h_inB : (x : X) ∈ B :=
    (interior_subset : interior B ⊆ B) hx_intB
  exact h_notB h_inB