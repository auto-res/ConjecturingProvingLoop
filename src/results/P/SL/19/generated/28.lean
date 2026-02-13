

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) :
    Topology.P3 (A := A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ interior (closure A) := hA hA_mem
      have hSubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hClos : closure A ⊆ closure (A ∪ B) := closure_mono (by
          intro z hz; exact Or.inl hz)
        exact interior_mono hClos
      exact hSubset hxA
  | inr hB_mem =>
      have hxB : x ∈ interior (closure B) := hB hB_mem
      have hSubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hClos : closure B ⊆ closure (A ∪ B) := closure_mono (by
          intro z hz; exact Or.inr hz)
        exact interior_mono hClos
      exact hSubset hxB