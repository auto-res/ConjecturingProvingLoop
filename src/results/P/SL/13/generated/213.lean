

theorem Topology.dense_implies_interior_closureInterior_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      interior (closure (interior (closure (A : Set X)))) = (Set.univ : Set X) := by
  intro hDense
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  calc
    interior (closure (interior (closure (A : Set X))))
        = interior (closure (interior (Set.univ : Set X))) := by
          simpa [h_cl]
    _ = interior (closure (Set.univ : Set X)) := by
          simp [interior_univ]
    _ = interior (Set.univ : Set X) := by
          simp [closure_univ]
    _ = (Set.univ : Set X) := by
          simp [interior_univ]