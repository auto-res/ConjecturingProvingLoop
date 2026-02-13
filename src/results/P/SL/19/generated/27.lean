

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) :
    Topology.P2 (A := A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ interior (closure (interior A)) := hA hA_mem
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hInt : interior A ⊆ interior (A ∪ B) := by
          have hSub : A ⊆ A ∪ B := by
            intro z hz; exact Or.inl hz
          exact interior_mono hSub
        have hClos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hInt
        exact interior_mono hClos
      exact hsubset hxA
  | inr hB_mem =>
      have hxB : x ∈ interior (closure (interior B)) := hB hB_mem
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hInt : interior B ⊆ interior (A ∪ B) := by
          have hSub : B ⊆ A ∪ B := by
            intro z hz; exact Or.inr hz
          exact interior_mono hSub
        have hClos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hInt
        exact interior_mono hClos
      exact hsubset hxB