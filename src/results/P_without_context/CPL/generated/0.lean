

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro h
  exact Set.Subset.trans h (interior_mono (closure_mono interior_subset))

theorem closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure A = closure (interior A) := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  ·
    exact closure_mono interior_subset

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  dsimp [P1]
  intro x hx
  simpa [interior_univ, closure_univ] using mem_univ x

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  simpa [P2] using (Set.empty_subset _)

theorem P3_open_set {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hA
  dsimp [P3]
  intro x hx
  exact (mem_interior).2 ⟨A, subset_closure, hA, hx⟩

theorem union_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`; use `hA`
      have hx_cl : x ∈ closure (interior A) := hA hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have hsubset : interior A ⊆ interior (A ∪ B) := by
        intro y hy
        exact (mem_interior).1 hy |> fun ⟨U, hUsub, hUopen, hyU⟩ =>
          (mem_interior).2 ⟨U, by
            intro z hz
            exact Or.inl (hUsub hz), hUopen,
            hyU⟩
      -- transport membership through `closure_mono`
      exact (closure_mono hsubset) hx_cl
  | inr hxB =>
      -- `x ∈ B`; use `hB`
      have hx_cl : x ∈ closure (interior B) := hB hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have hsubset : interior B ⊆ interior (A ∪ B) := by
        intro y hy
        exact (mem_interior).1 hy |> fun ⟨U, hUsub, hUopen, hyU⟩ =>
          (mem_interior).2 ⟨U, by
            intro z hz
            exact Or.inr (hUsub hz), hUopen,
            hyU⟩
      -- transport membership through `closure_mono`
      exact (closure_mono hsubset) hx_cl

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro h_closure
  dsimp [P3]
  intro x hx
  simpa [h_closure, interior_univ] using (Set.mem_univ x)