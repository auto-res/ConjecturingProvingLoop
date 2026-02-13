

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P3 A → Topology.P3 (A.prod (Set.univ : Set Y)) := by
  intro hA
  have hUniv : Topology.P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using
    (P3_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem exists_P1_between {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : Topology.P1 A) (hB : Topology.P1 B) : ∃ U, A ⊆ U ∧ U ⊆ B ∧ Topology.P1 U := by
  refine ⟨A ∪ interior B, ?_, ?_, ?_⟩
  · intro x hxA
    exact Or.inl hxA
  · intro x hxU
    cases hxU with
    | inl hxA  => exact hAB hxA
    | inr hxIB => exact interior_subset hxIB
  ·
    have hIntB : Topology.P1 (interior B) := P1_interior (A := B)
    have hUnion : Topology.P1 (A ∪ interior B) :=
      P1_union (A := A) (B := interior B) hA hIntB
    simpa using hUnion