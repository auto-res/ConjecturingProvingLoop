

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    P1 (X := X) (interior (closure A)) := by
  have hP2 : P2 (X := X) (interior (closure A)) :=
    P2_interior_closure (X := X) A
  exact P2_implies_P1 (X := X) (A := interior (closure A)) hP2