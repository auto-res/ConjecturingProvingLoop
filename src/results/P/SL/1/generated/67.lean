

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- First, retrieve the existing equivalences for open sets.
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Combine them into the desired equivalence with a conjunction.
  constructor
  · intro hP1
    exact And.intro (h1.mp hP1) (h2.mp hP1)
  · rintro ⟨hP2, _⟩
    exact h1.mpr hP2