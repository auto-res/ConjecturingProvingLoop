

theorem Topology.frontier_eq_compl_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) (hDense : closure A = (Set.univ : Set X)) :
    frontier A = Aᶜ := by
  calc
    frontier A = closure A \ interior A := rfl
    _ = (Set.univ : Set X) \ A := by
      simpa [hOpen.interior_eq, hDense]
    _ = Aᶜ := by
      ext x
      simp