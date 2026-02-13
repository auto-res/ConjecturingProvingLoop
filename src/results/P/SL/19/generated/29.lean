

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) :
    Topology.P1 (A := A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ closure (interior A) := hA hA_mem
      have hSubA : (A : Set X) ⊆ A ∪ B := by
        intro z hz; exact Or.inl hz
      have hIntSub : interior A ⊆ interior (A ∪ B) := interior_mono hSubA
      have hClosSub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hIntSub
      exact hClosSub hxA
  | inr hB_mem =>
      have hxB : x ∈ closure (interior B) := hB hB_mem
      have hSubB : (B : Set X) ⊆ A ∪ B := by
        intro z hz; exact Or.inr hz
      have hIntSub : interior B ⊆ interior (A ∪ B) := interior_mono hSubB
      have hClosSub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hIntSub
      exact hClosSub hxB