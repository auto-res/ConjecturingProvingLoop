

theorem P2_imp_closure_inter_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact (P1_iff_closure_inter_eq).1 (P2_imp_P1 hP2)

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense A → P3 A := by
  intro hDense
  intro x hx
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    have hCl : closure (A : Set X) = (Set.univ : Set X) :=
      (dense_iff_closure_eq).1 hDense
    simpa [hCl, interior_univ]
  simpa [hInt]