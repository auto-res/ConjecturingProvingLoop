

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : (Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A) := (P1_iff_P3_of_open (X:=X) (A:=A) hA).trans
    (P3_iff_P2_of_open (X:=X) (A:=A) hA)