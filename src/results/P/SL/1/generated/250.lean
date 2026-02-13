

theorem Topology.P3_diff_of_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) (hA : IsClosed A) :
    Topology.P3 (B \ A) := by
  -- The set `B \ A = B ∩ Aᶜ` is the intersection of two open sets,
  -- hence it is open.
  have hOpen : IsOpen (B \ A) :=
    hB.inter ((isOpen_compl_iff).2 hA)
  -- Every open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := B \ A) hOpen