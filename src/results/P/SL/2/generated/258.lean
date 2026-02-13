

theorem Topology.isOpen_P1_iff_P2_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A)) := by
  intro hOpen
  -- Auxiliary equivalences for an open set.
  have hP1P2 := (Topology.isOpen_P1_iff_P2 (A := A) hOpen)
  have hP1P3 := (Topology.isOpen_P1_iff_P3 (A := A) hOpen)
  constructor
  · intro hP1
    -- From `P1`, obtain `P2` and `P3` via the auxiliary equivalences.
    exact And.intro ((hP1P2).1 hP1) ((hP1P3).1 hP1)
  · rintro ⟨hP2, _hP3⟩
    -- Recover `P1` from `P2` using the equivalence for open sets.
    exact (hP1P2).2 hP2