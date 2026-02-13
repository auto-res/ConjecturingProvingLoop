

theorem dense_right_and_P3_left_implies_P3_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hDenseB : Dense B) (hP3A : Topology.P3 A) :
    Topology.P3 (A ×ˢ B) := by
  -- Apply the existing lemma to the swapped product `B ×ˢ A`.
  have hSymm :
      Topology.P3 (B ×ˢ A) :=
    dense_left_and_P3_right_implies_P3_prod
      (X := Y) (Y := X) (A := B) (B := A) hDenseB hP3A
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hSymm ⊢
  intro p hp
  -- Use the result for the swapped point `(p.2, p.1)`.
  have hSwapped : (p.2, p.1) ∈ B ×ˢ A := And.intro hp.2 hp.1
  have hIntSwapped := hSymm hSwapped
  -- Identify the interiors of the relevant closures.
  have hEqSource :
      interior (closure (B ×ˢ A)) =
        interior (closure B) ×ˢ interior (closure A) :=
    interior_closure_prod (X := Y) (Y := X) (A := B) (B := A)
  have hEqTarget :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  -- Transport membership through `hEqSource`.
  have hMemSource :
      (p.2, p.1) ∈ interior (closure B) ×ˢ interior (closure A) := by
    simpa [hEqSource] using hIntSwapped
  -- Extract coordinate-wise information.
  have hpB : p.2 ∈ interior (closure B) := (Set.mem_prod.1 hMemSource).1
  have hpA : p.1 ∈ interior (closure A) := (Set.mem_prod.1 hMemSource).2
  -- Assemble the membership for the original point.
  have hMemTarget :
      (p.1, p.2) ∈ interior (closure A) ×ˢ interior (closure B) :=
    And.intro hpA hpB
  simpa [hEqTarget] using hMemTarget