

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    Topology.P1 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ : Set X) := hB_closed.isOpen_compl
  -- Apply the lemma for the intersection with an open set.
  have hP1_inter :
      Topology.P1 (A ∩ Bᶜ : Set X) :=
    (Topology.P1_inter_open (A := A) (B := Bᶜ) hOpenCompl) hP1A
  simpa [Set.diff_eq] using hP1_inter