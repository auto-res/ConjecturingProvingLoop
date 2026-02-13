

theorem P1_iff_P2_and_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ↔
      (Topology.P2 (interior (A : Set X)) ∧ Topology.P3 (interior (A : Set X))) := by
  -- Pairwise equivalences for the open set `interior A`.
  have h₁ :
      Topology.P1 (interior (A : Set X)) ↔
        Topology.P2 (interior (A : Set X)) :=
    (Topology.P1_iff_P2_of_interior (X := X) (A := A))
  have h₂ :
      Topology.P2 (interior (A : Set X)) ↔
        Topology.P3 (interior (A : Set X)) :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  -- Assemble the desired equivalence.
  constructor
  · intro hP1
    -- Convert `P1` into `P2`, then into `P3`.
    have hP2 : Topology.P2 (interior (A : Set X)) := (h₁).1 hP1
    have hP3 : Topology.P3 (interior (A : Set X)) := (h₂).1 hP2
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    -- Convert `P2` back into `P1` using the first equivalence.
    exact (h₁).2 hP2