

theorem Topology.interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = Set.univ := by
  constructor
  · intro hInt
    apply Set.Subset.antisymm
    · exact Set.Subset_univ
    · intro x _
      -- Since `interior (closure A) = univ`, every point lies in this interior,
      -- hence in `closure A`.
      have hxInt : (x : X) ∈ interior (closure A) := by
        simpa [hInt] using (by simp : x ∈ (Set.univ : Set X))
      exact interior_subset hxInt
  · intro hCl
    exact
      Topology.interior_closure_eq_univ_of_dense
        (X := X) (A := A) hCl