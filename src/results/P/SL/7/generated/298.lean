

theorem Topology.P3_inter_open_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) :
    Topology.P3 (A ∩ B ∩ C : Set X) := by
  -- `A` is open, hence satisfies `P3`.
  have hP3A : Topology.P3 (A : Set X) :=
    (Topology.IsOpen_P1_and_P3 (A := A) hA).2
  -- Intersect `A` with the open set `B`.
  have hP3AB : Topology.P3 (A ∩ B : Set X) :=
    Topology.P3_inter_open (A := A) (U := B) hP3A hB
  -- Intersect the result with the open set `C`.
  have hP3ABC : Topology.P3 ((A ∩ B) ∩ C : Set X) :=
    Topology.P3_inter_open (A := A ∩ B) (U := C) hP3AB hC
  -- Reassociate intersections to match the statement.
  simpa [Set.inter_assoc] using hP3ABC