

theorem Topology.P1_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P1 (X:=X) B) :
    Topology.P1 (X:=X) (A ∩ B) := by
  -- Use commutativity of `∩` and the existing lemma `P1_inter_left_of_open`.
  have h := Topology.P1_inter_left_of_open (X:=X) (A:=B) (B:=A) hPB hA_open
  simpa [Set.inter_comm] using h