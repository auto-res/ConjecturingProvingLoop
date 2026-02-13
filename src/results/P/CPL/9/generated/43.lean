

theorem P2_prod_five {W Y Z : Type*} [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P2 (A := A)) (hB : P2 B) (hC : Topology.P2 (A := C)) (hD : Topology.P2 (A := D)) : Topology.P2 (A := Set.prod A (Set.prod B (Set.prod C D))) := by
  -- First, build `P2` for the auxiliary product `B × (C × D)`.
  have hBCD : Topology.P2 (A := Set.prod B (Set.prod C D)) := by
    simpa using
      (Topology.P2_prod_three
        (A := B) (B := C) (C := D)
        (hA := hB) (hB := hC) (hC := hD))
  -- Then combine it with `A`.
  simpa using
    (Topology.P2_product
      (A := A)
      (B := Set.prod B (Set.prod C D))
      hA
      hBCD)

theorem P3_closed_complement {A : Set X} (hA : IsClosed A) : P3 Aᶜ := by
  apply P3_of_open
  simpa using hA.isOpen_compl

theorem P3_prod_four_univ {Y Z W : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W] : P3 (Set.prod (Set.univ : Set X) (Set.prod (Set.univ : Set Y) (Set.prod (Set.univ : Set Z) (Set.univ : Set W)))) := by
  -- Each factor `Set.univ` satisfies `P3`.
  have hX : Topology.P3 (A := (Set.univ : Set X)) := by
    simpa using Topology.P3_univ (X := X)
  have hY : Topology.P3 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P3_univ (X := Y)
  have hZ : Topology.P3 (A := (Set.univ : Set Z)) := by
    simpa using Topology.P3_univ (X := Z)
  have hW : Topology.P3 (A := (Set.univ : Set W)) := by
    simpa using Topology.P3_univ (X := W)
  -- Build `P3` for `Z × W`.
  have hZW :
      Topology.P3 (A := Set.prod (Set.univ : Set Z) (Set.univ : Set W)) :=
    Topology.P3_prod
      (A := (Set.univ : Set Z)) (B := (Set.univ : Set W)) hZ hW
  -- Build `P3` for `Y × (Z × W)`.
  have hY_ZW :
      Topology.P3
        (A := Set.prod (Set.univ : Set Y)
              (Set.prod (Set.univ : Set Z) (Set.univ : Set W))) :=
    Topology.P3_prod
      (A := (Set.univ : Set Y))
      (B := Set.prod (Set.univ : Set Z) (Set.univ : Set W)) hY hZW
  -- Finally, build the desired product with `X`.
  simpa using
    (Topology.P3_prod
      (A := (Set.univ : Set X))
      (B := Set.prod (Set.univ : Set Y)
            (Set.prod (Set.univ : Set Z) (Set.univ : Set W)))
      hX hY_ZW)