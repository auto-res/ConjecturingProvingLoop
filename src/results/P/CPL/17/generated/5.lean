

theorem P3_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure A) := hP3A hxA
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hclosure : closure A ⊆ closure (A ∪ B) := by
          have h : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact closure_mono h
        exact interior_mono hclosure
      exact hsubset hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure B) := hP3B hxB
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hclosure : closure B ⊆ closure (A ∪ B) := by
          have h : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact closure_mono h
        exact interior_mono hclosure
      exact hsubset hx_int