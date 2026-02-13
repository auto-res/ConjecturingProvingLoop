

theorem dense_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure A = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have hIntCl : interior (closure A) = (Set.univ : Set X) := by
    have : interior (closure A) = interior (Set.univ : Set X) := by
      simpa [hA]
    simpa [interior_univ] using this
  have hAu : A ⊆ (Set.univ : Set X) := by
    intro x hx
    trivial
  simpa [hIntCl] using hAu