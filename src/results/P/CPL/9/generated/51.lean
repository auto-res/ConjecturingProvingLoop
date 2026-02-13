

theorem P3_prod_five_univ {X Y Z W V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V] : Topology.P3 (A := Set.prod (Set.univ : Set X) (Set.prod (Set.univ : Set Y) (Set.prod (Set.univ : Set Z) (Set.prod (Set.univ : Set W) (Set.univ : Set V))))) := by
  -- Each factor `Set.univ` satisfies `P3`.
  have hX : Topology.P3 (A := (Set.univ : Set X)) := by
    simpa using Topology.P3_univ (X := X)
  have hY : Topology.P3 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P3_univ (X := Y)
  have hZ : Topology.P3 (A := (Set.univ : Set Z)) := by
    simpa using Topology.P3_univ (X := Z)
  have hW : Topology.P3 (A := (Set.univ : Set W)) := by
    simpa using Topology.P3_univ (X := W)
  have hV : Topology.P3 (A := (Set.univ : Set V)) := by
    simpa using Topology.P3_univ (X := V)
  -- Build `P3` for `W × V`.
  have hWV :
      Topology.P3 (A := Set.prod (Set.univ : Set W) (Set.univ : Set V)) :=
    Topology.P3_prod
      (A := (Set.univ : Set W)) (B := (Set.univ : Set V)) hW hV
  -- Build `P3` for `Z × (W × V)`.
  have hZ_WV :
      Topology.P3
        (A := Set.prod (Set.univ : Set Z)
              (Set.prod (Set.univ : Set W) (Set.univ : Set V))) :=
    Topology.P3_prod
      (A := (Set.univ : Set Z))
      (B := Set.prod (Set.univ : Set W) (Set.univ : Set V))
      hZ hWV
  -- Build `P3` for `Y × (Z × (W × V))`.
  have hY_ZWV :
      Topology.P3
        (A := Set.prod (Set.univ : Set Y)
              (Set.prod (Set.univ : Set Z)
                (Set.prod (Set.univ : Set W) (Set.univ : Set V)))) :=
    Topology.P3_prod
      (A := (Set.univ : Set Y))
      (B := Set.prod (Set.univ : Set Z)
            (Set.prod (Set.univ : Set W) (Set.univ : Set V)))
      hY hZ_WV
  -- Finally, combine with `X`.
  simpa using
    (Topology.P3_prod
      (A := (Set.univ : Set X))
      (B := Set.prod (Set.univ : Set Y)
            (Set.prod (Set.univ : Set Z)
              (Set.prod (Set.univ : Set W) (Set.univ : Set V))))
      hX hY_ZWV)

theorem P2_comp_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 (A := A) := by
  have hP1 : P1 (A := A) := P1_subsingleton (A := A)
  have hP3 : P3 (A := A) := P3_subsingleton (A := A)
  exact P1_and_P3_imp_P2 (A := A) hP1 hP3