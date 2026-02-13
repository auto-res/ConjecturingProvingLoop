

theorem Topology.P1_P2_P3_iff_isClopen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsClopen A := by
  -- First, use the existing equivalence between the triple property and openness.
  have hOpenEquiv :
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A :=
    Topology.P1_P2_P3_iff_isOpen_of_isClosed (A := A) hA
  -- Establish the desired equivalence with clopeness.
  constructor
  · -- From the triple property, deduce openness and hence clopeness.
    intro hTriple
    have hOpen : IsOpen A := hOpenEquiv.mp hTriple
    exact ⟨hA, hOpen⟩
  · -- From clopeness, obtain openness and hence the triple property.
    intro hClopen
    have hOpen : IsOpen A := hClopen.2
    exact hOpenEquiv.mpr hOpen