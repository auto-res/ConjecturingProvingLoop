

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) : Topology.P1 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  -- First, build `P1` for the triple product `A ×ˢ B ×ˢ C`.
  have hABC : Topology.P1 (Set.prod (Set.prod A B) C) :=
    Topology.P1_prod_three (A := A) (B := B) (C := C) hA hB hC
  -- Then combine it with `D`.
  simpa using
    (Topology.P1_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD)

theorem P2_univ_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : Topology.P2 (Set.prod (Set.univ : Set X) (Set.univ : Set Y)) := by
  have hX : Topology.P2 (Set.univ : Set X) := Topology.P2_univ (X := X)
  simpa using
    (Topology.P2_prod_univ (X := X) (Y := Y) (A := (Set.univ : Set X)) hX)