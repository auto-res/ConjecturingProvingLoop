

theorem P1_prod_swap_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P1 (A.prod B) ↔ Topology.P1 (B.prod A)) := by
  constructor
  · intro h
    exact P1_prod_swap (X := X) (Y := Y) (A := A) (B := B) h
  · intro h
    simpa using
      (P1_prod_swap (X := Y) (Y := X) (A := B) (B := A) h)