

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro h
  exact subset_trans h interior_subset

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hxB

theorem P1_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  classical
  by_cases hA : (A : Set X) = (∅ : Set X)
  · -- `A` is empty, the claim is immediate
    simpa [Topology.P1, hA] using (Set.empty_subset _)
  · -- `A` is non–empty
    -- first show that `A = univ`
    have h_univ : (A : Set X) = Set.univ := by
      -- obtain a point of `A`
      have hne : (A : Set X).Nonempty := by
        cases (Set.eq_empty_or_nonempty (A : Set X)) with
        | inl h_eq =>
            exact (hA h_eq).elim
        | inr h_nonempty =>
            exact h_nonempty
      rcases hne with ⟨x, hx⟩
      -- every point of `X` is that point
      apply (Set.eq_univ_iff_forall).2
      intro y
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
    -- now conclude the desired inclusion
    simpa [Topology.P1, h_univ, interior_univ, closure_univ] using
      (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)