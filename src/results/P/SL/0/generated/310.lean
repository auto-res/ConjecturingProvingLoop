

theorem closure_inter_three_subset_inter_closures
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure ((A ∩ B ∩ C) : Set X) ⊆
      closure (A : Set X) ∩ closure (B : Set X) ∩ closure (C : Set X) := by
  intro x hx
  -- Each of `A`, `B`, and `C` contains `A ∩ B ∩ C`, hence their closures
  -- contain `closure (A ∩ B ∩ C)`.
  have hSubA : (A ∩ B ∩ C : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact (hy.1).1
  have hSubB : (A ∩ B ∩ C : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact (hy.1).2
  have hSubC : (A ∩ B ∩ C : Set X) ⊆ (C : Set X) := by
    intro y hy
    exact hy.2
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  have hxC : x ∈ closure (C : Set X) := (closure_mono hSubC) hx
  exact And.intro (And.intro hxA hxB) hxC