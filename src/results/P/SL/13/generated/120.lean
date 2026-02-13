

theorem Topology.dense_of_P1_and_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hDenseInt : Dense (interior (A : Set X))) :
    Dense (A : Set X) := by
  dsimp [Dense] at hDenseInt ⊢
  have h_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  simpa [h_eq] using hDenseInt