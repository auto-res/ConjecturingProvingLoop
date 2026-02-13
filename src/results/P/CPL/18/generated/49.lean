

theorem P3_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) (hE : Topology.P3 E) : Topology.P3 ((((A.prod B).prod C).prod D).prod E) := by
  -- First, obtain `P3` for `A × B`.
  have hAB : Topology.P3 (A.prod B) :=
    P3_prod (X := V) (Y := W) (A := A) (B := B) hA hB
  -- Next, obtain `P3` for `(A × B) × C`.
  have hABC : Topology.P3 ((A.prod B).prod C) :=
    P3_prod
      (X := V × W) (Y := X)
      (A := (A.prod B)) (B := C) hAB hC
  -- Then, obtain `P3` for `((A × B) × C) × D`.
  have hABCD : Topology.P3 (((A.prod B).prod C).prod D) :=
    P3_prod
      (X := (V × W) × X) (Y := Y)
      (A := ((A.prod B).prod C)) (B := D) hABC hD
  -- Finally, combine this set with `E`.
  have hABCDE : Topology.P3 ((((A.prod B).prod C).prod D).prod E) :=
    P3_prod
      (X := ((V × W) × X) × Y) (Y := Z)
      (A := (((A.prod B).prod C).prod D)) (B := E) hABCD hE
  simpa using hABCDE