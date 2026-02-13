

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) : Topology.P1 (((A.prod B).prod C).prod D) := by
  -- First, obtain `P1` for `(A × B) × C`.
  have hABC : Topology.P1 ((A.prod B).prod C) :=
    P1_prod_three (X := W) (Y := X) (Z := Y) (A := A) (B := B) (C := C) hA hB hC
  -- Then combine this set with `D`.
  have hABCD : Topology.P1 (((A.prod B).prod C).prod D) :=
    P1_prod
      (X := (W × X) × Y)
      (Y := Z)
      (A := (A.prod B).prod C)
      (B := D)
      hABC
      hD
  simpa using hABCD